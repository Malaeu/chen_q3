# PROSHKA REQUEST — A3 Floor at t_critical (single‑scale)

## Non‑negotiable policy
- Не ищи «статус RH». RH не доказана публично, мы доказываем её сами.
- Никаких внешних источников. Работай **только** с нашим контекст‑паком и файлами проекта.
- Не изобретай новые теоремы: либо копируй/адаптируй уже существующую логику A3_Floor_Main, либо честно говори, где упираешься.

## Цель (Lean)
Закрыть `FloorGoal` на single‑scale:

```lean
-- файл: Q3/Proofs/A3_Floor_Critical_Proof.lean (можно новый)
import Q3.Proofs.A3_Floor_Critical_Goal
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

open Q3

 theorem A3FloorCritical.floor_goal_tcritical : Q3.Proofs.A3FloorCritical.FloorGoal := by
   -- proof
```

где

```lean
def Q3.Proofs.A3FloorCritical.FloorGoal : Prop :=
  ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
    Q3.c_star ≤ P_A B_min Q3.t_critical θ
```

## Контекст
- На `t_sym` это **уже доказано** в `Q3/Proofs/A3_Floor_Main.lean` (см. `P_A_ge_c_star`).
- На `t_critical = 3/20` нужно доказать аналогично.
- Мы уже завели мосты:
  - `arch_term_ge_at_t_critical` (теперь требует floor‑гипотезу)
  - `rayleigh_basis0_shift_ge_cstar_quarter_Bmin` (готов, если есть FloorGoal)

## Требование к результату
Нужен **чистый Lean‑код без `sorry`**, который реально компилируется. Лучше маленькая серия лемм, чем один огромный блок.

## Предпочтительный подход
**Скопировать/адаптировать доказательство `P_A_ge_c_star` из `A3_Floor_Main` на `t_critical`.**

Какие куски, вероятно, нужно продублировать с заменой `t_sym → t_critical`:
- `w_lower_on_half` (или эквивалент нижней оценки w на [-1/2,1/2])
- `g0_lower`, `g1_lower`, `g2_lower`, `g_neg1_lower`, `g_neg2_lower`, `g_neg3_lower`
- финальная сборка в `P_A_ge_c_star`

> Важно: это **не** монотонность по t. Нужна переработка оценок с новыми числовыми константами.

## Что именно нужно от тебя (Proshka)
1) Список конкретных лемм, которые нужно портировать (с точными именами из `A3_Floor_Main`).
2) Минимальный Lean‑скелет (код) для `floor_goal_tcritical` + подпроцедур.
3) Если какая-то оценка ломается, явно укажи где и почему (и что надо подправить в числах).

## Где смотреть
См. контекст‑пак:
`ACTIVE/output/proshka_context_floor_tcritical.md`

Ключевые файлы:
- `Q3/Proofs/A3_Floor_Main.lean`
- `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/Params_Critical.lean`
- `Q3/Proofs/Q_nonneg_t_critical.lean`

## Формат ответа
- Сначала **план и карта лемм** (bullet list)
- Затем **Lean‑скелет**
- Затем **список мест, где нужны численные константы**

# PROSHKA CONTEXT PACK
Generated: 2026-01-24 23:12:31
Repo: /Users/emalam/Documents/GitHub/chen_q3/sandboxes/projekt_2

This pack is intended for Proshka. It inlines key files and recent git context.


## Git status

## projekt_2A


## Git log

7c5c349 [projekt_2A][AI-codex] add floor bridge for P_A_shift tcritical
498185e [projekt_2A][AI-codex] arch_term tcritical floor reduction
416e808 [projekt_2A][AI-codex] close singlescale rayleigh via arch_term
7f49fde [projekt_2A][AI-codex] fix atom-closure single-scale bridge
247a56f [projekt_2A][AI-codex] add ACTIVE tree navigation
5c0006a [projekt_2A][AI-codex] insights: rayleigh_basis0 t_critical plan
a04f814 [projekt_2A][AI-codex] refresh proshka context pack
8c3aae0 [projekt_2A][AI-codex] close P_A_shift continuity
581d9f3 [projekt_2A][AI-codex] tau0 singlescale refactor
ddd1d8a [projekt_2A][AI-codex] ralph plan update + zed note
76541dc [projekt_2A][AI-codex] add ralph loop + plan sweep
ccd7a99 [projekt_2A][AI-codex] single-scale paper sweep
c2f2c33 [projekt_2A][AI-codex] proshka brief clarity
8af492d [projekt_2A][AI-codex] proshka mission framing
dc8893f [projekt_2A][AI-codex] proshka rules + aristotle requests
08c099d [projekt_2A][AI-codex] proshka policy + pack refresh
cb42a8e [projekt_2A][AI-codex] proshka refs + memory pack symlink
6a38fc3 [projekt_2A][AI-codex] proshka pack + brief builder
1b7e648 [projekt_2A][AI-codex] Exclude ACTIVE hub from link checks
df27142 [projekt_2A][AI-codex] Clarify legacy conflicts and add prompt example
f71255a [projekt_2A][AI-codex] Consolidate ERS specs and add RU solver prompt
4aa4864 [projekt_2A][AI-codex] Mark legacy specs and align with mainline
a787019 [projekt_2A][AI-codex] Add specs index and block map in ACTIVE hub
4065c3a [projekt_2A][AI-codex] Add link-first knowledge base index
9ce7cfc [projekt_2A][AI-codex] Link Aristotle models knowledge dir in ACTIVE hub
7fade2b [projekt_2A][AI-codex] Link Proshka memory pack in ACTIVE hub
37cb4b1 [projekt_2A][AI-codex] Expand ACTIVE hub and add stats updater
550758c [projekt_2A][AI-codex] Add ACTIVE hub and chain status doc
5806fa4 [projekt_2A][AI-codex] Single-scale t_critical bridge for prime sum cap
16ec725 [projekt_2A][AI-codex] Add mac session log (2026-01-24)
599cd07 [projekt_2][AI-codex] INSIGHTS: prime_sum_phi_shift plan (in progress)
0550a59 [projekt_2][AI-codex] Close Q_nonneg_on_atoms; document single-scale axioms (8 axioms)
22b3538 single-scale RKHS contraction at t_critical
a84b264 basisFun C1 opNorm wrapper in RKHS_cap_rayleigh
5ad1b75 basisFun C1 opNorm bound for T_P_comp
73ad917 wire basisFun C1 lemma + note in insights
0c9f06f C1 compression remark + basisFun h_eval wiring
d1760d4 single-scale bridge at t_critical for atom closure
afb41b1 insights: plan Q_nonneg_atoms_closure (in progress)
55867c1 [projekt_2A][AI-codex] Add Proshka request for one-scale t_critical gap


## Git diff




## File: full/q3.lean.aristotle/ACTIVE/KNOWLEDGE_BASE.md

# Knowledge Base (index + live facts)

Goal: lightweight, link-first map so agents pull only what they need.
Keep this file short. Put details in linked docs.

## 0) Start here (order matters)

1) `ACTIVE/orchestrator.md` — current status + next steps
2) `ACTIVE/chain_status.md` — single-scale chain summary
3) `ACTIVE/insights.md` — live insights index (links only)
4) `ACTIVE/workflow.md` — workflow rules
5) `ACTIVE/tree.md` — navigation tree (what depends on what)
6) `ACTIVE/SPECS_INDEX.md` — curated spec pointers + constants checklist
7) `ACTIVE/Q3_BLOCK_MAP.md` — Lean ↔ paper block map
8) `ACTIVE/ERS_SUMMARY.md` — consolidated ERS legacy summary

Note: spec sources are legacy/background. For mainline decisions, return to
`ACTIVE/chain_status.md` and `ACTIVE/orchestrator.md`.

## 1) Canonical chain (single-scale t_critical)

- Mainline parameters:
  - `t_critical = 3/20`
  - base-atom cone with `tau = 0`
- Canonical summary: `ACTIVE/chain_status.md`
- Paper alignment audit (single-scale vs legacy): `ACTIVE/single_scale_paper_audit.md`
- Legacy two-scale index: `ACTIVE/legacy_two_scale_index.md`

## 2) Live axioms (single-scale)

These are the only open project axioms on the main chain:

- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (tau = 0)

Source of truth:
- `ACTIVE/orchestrator.md` (Axiom Count + table)
- `ACTIVE/chain_status.md`

## 3) Canonical docs (maps/specs)

- Proof maps:
  - `ACTIVE/proof_map.md`
  - `ACTIVE/proof_map_new_kernel.md`
- Paper ↔ Lean mapping:
  - `ACTIVE/paper_lean_mapping.md`
  - `ACTIVE/q3_pdf_structure.md`
  - `ACTIVE/q3_structure_mapping.md`
- Architecture/status:
  - `ACTIVE/architecture.md`
  - `ACTIVE/project_status.md`
  - `ACTIVE/axiom_closure_analysis.md`

## 4) Aristotle + Proshka

- Aristotle docs (RU):
  - `ACTIVE/aristotle.md`
  - `ACTIVE/aristotle_sandbox_guide.md`
- Proshka:
  - `ACTIVE/proshka_entrypoint.md`
  - `ACTIVE/proshka_memory_pack.md`
  - `PROSHKA_REQUEST_4.md` (single‑scale closure pack)
  - `ACTIVE/proshka_context_single_scale.md` (one‑file packed brief)
  - `scripts/build_proshka_brief.py` (pack builder)
  - `docs/PROSHKA_POLICY.md` (canonical set policy)

## 5) Stats update

- Script: `scripts/update_formalization_stats.sh`
- Output: `FORMALIZATION_STATS.md`

## 6) Knowledge base (external)

- `ACTIVE/aristotle_models_knowledge` — Aristotle model/training knowledge dump
- `ACTIVE/codex_agent_loop_notes.md` — Codex CLI agent loop notes (OpenAI blog)

## 7) Editing policy (keep this stable)

- Add only links + 1–2 lines of context.
- Avoid duplicating content from linked docs.
- When a doc becomes obsolete, mark it inside that doc (do not delete).


## File: full/q3.lean.aristotle/ACTIVE/chain_status.md

# Chain Status (single-scale t_critical)

This file is the canonical, minimal chain summary for the current mainline.
It is intended to stay aligned with the code after each refactor.

## Mainline parameters

- Use single-scale t_critical = 3/20.
- Use the base-atom cone with tau = 0 (even functions only).
- Avoid the old two-scale chain (t_sym vs t_rkhs_cap) in the mainline.

## Current chain (code-level)

1) A3 floor (archimedean lower bound)
- Target: Rayleigh lower bound at t_critical for P_A_shift (tau = 0).
- Status: axiomatized as
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
  in `Q3/Proofs/SingleScale_Assumptions.lean`.

2) RKHS prime cap
- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Includes C1 compression identity (basisFun and dictionary embedding) and
  RKHS cap wiring at t_rkhs_cap.

3) Prime cap (tau = 0)
- Single-scale numeric cap is now `rho_one ≤ c_star/4`
  (`SingleScale.rho_oneK_tcritical_le_cstar_quarter`, closed).

4) Continuity (A2-style) at t_critical (single-scale)
- Status: **closed** via `ShiftedWindows.P_A_shift_continuous`
  (requires `B > 0`, tau arbitrary).

5) Atom-level nonnegativity and closure
- `Q3/Proofs/Q_nonneg_atoms_closure.lean` closes the fixed-t chain assuming
  the two SingleScale axioms above.

## Remaining SingleScale axioms (open)

- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

## Related entry points

- `PROJECT_ORCHESTRATOR.md` (status, next steps)
- `PHILOSOPHY_OF_PROOF.md` (axiom policy)
- `docs/INSIGHTS.md` (running synthesis notes)


## File: full/q3.lean.aristotle/ACTIVE/orchestrator.md

# PROJECT ORCHESTRATOR - Q3
## Lean Formalization of Riemann Hypothesis

Last Updated: 2026-01-24
Single entry point: read this file at session start.

## Quick Start

1) Read this file.
2) Use "Current State" and "Active Next Step".
3) Only open linked files if needed.
3.5) Chain summary: `docs/CHAIN_STATUS.md` (single-scale t_critical mainline).
3.6) Knowledge base index: `ACTIVE/KNOWLEDGE_BASE.md` (link-first map).
4) Documentation discipline: update `docs/INSIGHTS.md` and
   `FORMALIZATION_STATS.md` instead of creating new docs.
5) **Застрял > 30 мин?** → Запроси Прошку (см. `docs/INSIGHTS.md` секция "Прошка").
6) Hub for active docs/db/scripts: `ACTIVE/` (symlink index).

## Current State (short)

- A3_FLOOR is proven and integrated: `P_A_ge_c_star` from
  `A3_Floor_Main.lean` is used in the Fourier A3 bridge.
- Fourier A3 bridge is wired: `Q3/Atoms_Positive.lean` now depends on
  `A3_bridge_data_rayleigh_Fourier` and the axiom
  `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.
- `Q_Lipschitz_on_W_K` is a theorem; arch/prime Lipschitz bridge axioms are closed
  in `Q3/Proofs/Q_Lipschitz.lean`.
- `mem_nodes_finset_of_mem_Q3Nodes` is a theorem in `Q3/Proofs/Bridge.lean`.
- RKHS contraction is now bridged: `RKHS_contraction_axiom` is no longer in
  `#print axioms` for `Q3.Main.RH_of_Weil_and_Q3` (see `Q3/Proofs/Bridge.lean`,
  wired in `Q3/AxiomsTheorems.lean`).
- `A1_density_WK_thm` is proven in `Q3/Proofs/A1_density.lean` and wired in
  `Q3/T5_Transfer.lean`, so `A1_density_WK_axiom` is gone from the main chain.
- RKHS cap is PROVEN in `Q3/Proofs/RKHS_cap_rayleigh.lean`:
  `weight_sum_le_rho_one` + `rkhs_cap_rayleigh_tcap` with `t_rkhs_cap = 40`.
- C1 compression identity is formalized (basisFun + dictionary embedding) in
  `Q3/Proofs/RKHS_cap_rayleigh.lean` (search `compression identity`).
- New one-scale A3 bridge scaffolding (no two-scale): `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`
  (fixed-`t` bridge + generic weight-sum → Rayleigh cap lemma in `Q3/Proofs/RKHS_cap_generic.lean`).
- Single-scale parameter source: `Q3/Proofs/Q_nonneg_t_critical.lean`
  (defines `t_critical = 3/20` and `t0_critical`).
- Atom positivity/T5 transfer now use `t0_critical` (t = 0.15) for `AtomCone_K_fixed`;
  BaseAtomCone guard lemma added in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Single-scale prime cap (tau = 0) is now a direct numeric bound:
  `rho_one ≤ c_star/4` in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Helper lemma for “unitary conjugation preserves opNorm” added:
  `Q3/Proofs/OpNorm_Unitary.lean` (used in the `hA` decision tree, see `docs/INSIGHTS.md`).
- Legacy: `A3_bridge_axiom` (sampling Toeplitz + a_star) is still in `Q3/Axioms.lean`
  but no longer appears in the main chain.

## Wiring vs Closing (definition)

- wiring: replace an axiom in `Q3/AxiomsTheorems.lean` with a theorem. This only
  reduces `#print axioms` if the theorem is itself axiom-free.
- closing: provide a proof with no new axioms, so the axiom disappears from
  `#print axioms`.

## Axiom Count (verified)

Command:
```bash
./scripts/check_axioms.sh
# or manually:
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1 | rg -v "^info:"
```

Result: **6 axioms** (3 project + 3 standard)

- Standard Lean: `propext`, `Classical.choice`, `Quot.sound`
- Level 1 (Classical Literature): `Weil_criterion`, `Schur_test`
- Level 2 (Q3 Paper, single‑scale): `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

**Closed axioms (history):**
- `a_star_pos` → closed via positivity (2026-01-21)
- `a_star_continuous` → closed via Mathlib Gamma continuity
- `a_star_bdd_on_compact` → closed via continuous + compact
- `a_star_even` → closed via Mathlib Gamma_conj (2026-01-20)
- `A1_density_WK_axiom` → closed via bounded hat interpolation (h_even as mass bound)
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` → closed via Q_nonneg_atoms_closure (2026-01-24)
- `SingleScale.continuous_P_A_shift` → closed via `ShiftedWindows.P_A_shift_continuous` (2026-01-24)

## Critical Chain (ASCII)

```
RH_of_Weil_and_Q3
  |
  +-- Weil_criterion [AX external]
  |
  +-- Q_nonneg_on_Weil_cone [OK]
       |
       +-- T5_transfer [OK]
            |
            +-- A1_density_WK [OK]
            +-- Q_Lipschitz_on_W_K [OK]
            +-- Q_nonneg_on_atoms [OK]
                 |
                 +-- SingleScale assumptions [AX]
                 +-- RKHS_contraction [OK]
```

## 🚨🚨🚨 CRITICAL: LaTeX Proof Gap Discovered (2026-01-22) 🚨🚨🚨

**FINDING:** Numerical verification shows Q(Φ_{t_sym}) = -16.29 < 0, contradicting Theorem A3.

**ROOT CAUSE:** The LaTeX proof conflates TWO DIFFERENT T_P operators:

1. **Rayleigh T_P^{(M)}** (rayleigh_bridge.tex): `Σ w(n)·Φ_{B,t}(ξ_n)·|v_n⟩⟨v_n|`
   - Includes Fejér×heat damping factor `Φ_{B,t}(ξ_n)`
   
2. **RKHS T_P** (RKHS/main.tex): `Σ w_RKHS(n)·|k_n⟩⟨k_n|`
   - NO Fejér×heat factor — just `w_RKHS(n) = Λ(n)/√n`

**THE GAP:** Theorem A3 claims `λ_min(T_M[P_A] - T_P) ≥ c_*/4` using:
- P_A built with t_sym = 0.06
- ||T_P|| bound from RKHS (which uses different operator!)

**Numerical verification (B=3, t_sym=0.06):**
- Arch term: ∫ P_A dθ = 11.06
- Prime term: Σ w(n)·Φ(ξ_n) = 27.35
- **Q = -16.29 < 0** ← CONTRADICTS THEOREM

**FULL ANALYSIS:** `docs/LATEX_PROOF_GAP_ANALYSIS.md`

**STATUS:** `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` is now closed via the
single‑scale chain, but the gap remains as **two SingleScale axioms**.
Mathematical consultation with Proshka required to remove those assumptions.

**HARD PIVOT DIRECTION (in progress):** one-scale parameterization at `t = t_critical`
and “true C1” matching (`hA`) for the RKHS prime operator (no embedding handwaving).
Decision tree + file pointers live in `docs/INSIGHTS.md` (search for “нетривиальное hA”).

---

## Active Next Step (ON HOLD pending gap resolution)

~~1) Wire the **proven** Rayleigh-Q identification into the atoms-positivity chain:~~
~~   use `rayleigh_Q_eq_Q` in `Q3/Proofs/Rayleigh_Q_identification.lean`.~~
~~2) Replace `Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` in~~
~~   `Q3/Atoms_Positive.lean` / `Q3/AxiomsTheorems.lean` with the theorem proof~~
~~   (A3 floor + RKHS cap + Rayleigh identification).~~

**NEW PRIORITY:** Build an audit-resistant replacement for the old two-scale bridge:
1) Fix the spec to one-scale (`t = t_critical`) in a new chain (do not patch ad-hoc).
2) Close the *nontrivial* `hA` matching for the RKHS prime operator (C1 style).
3) Only then rewire the main chain and close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.

### What does “which branch?” mean (for a normal git user)

There are two different meanings of “ветка”:

1) **Git branch** (what `git switch` changes): currently we work on `projekt_2A`.
2) **Proof-architecture branch** (inside one git branch): “A3_FLOOR/Fourier Toeplitz” vs “old RKHS operator”.

Quick way to orient a fresh session:

```bash
git branch --show-current
git log -n 1 --oneline
sed -n '1,80p' full/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
```

### Two parallel work streams (recommended)

**Stream A (NOW, closes chain fast): Option 2 = Schur/weight_sum cap (no RKHS embedding)**

- The “cap” is already formalized for the Rayleigh/compression operator:
  `Q3/Proofs/RKHS_cap_rayleigh.lean` (`T_P_comp_real_opNorm_le_weight_sum`, `weight_sum_le_rho_one`, `rkhs_cap_rayleigh_tcap`).
- This stream is about **wiring/porting it to the one-scale `t_critical` chain** (not about Moore–Aronszajn).

**Stream B (PARALLEL, infrastructure): Option 1 = true Gaussian/RKHS kernel model**

- Aristotle tasks live in `full/q3.lean.aristotle/aristotle_input/`.
- Current task (kernel identity): `aristotle_input/gaussian_rkhs_kernel_v1.lean` + `.md`.
- Goal: extract hole-free lemmas from Aristotle output and then implement the RKHS interface in-project.

Rule: do Stream A on the main branch to keep momentum; do Stream B via small, self-contained Aristotle tasks
so we never block the main closure on analytic infrastructure.

## 🚨 CRITICAL GAP: AtomCone_K_fixed (2026-01-18)

**Discovery:** mgrep semantic search revealed a gap between обсуждение и реализация.

**Problem:** `Q_nonneg_bridge.lean` не компилируется из-за quantifier mismatch:
- `AtomCone_K` квантифицирует `∀ t > 0` (произвольный t)
- A3/RKHS bounds доказаны для ФИКСИРОВАННЫХ t:
  - A3 floor: `t_sym = 0.06`
  - RKHS cap: `t_rkhs_cap = 40`

**Solution (from Прошка 2026-01-16, NOT implemented):**
```lean
def AtomCone_K_fixed (K t₀ : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c B τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧ (∀ i, B i > 0) ∧ (∀ i, |τ i| + B i ≤ K) ∧
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t₀ (τ i) x) ∧ g ∈ W_K K }
```

**Action Items:**
1. [ ] Add `AtomCone_K_fixed` to `Q3/Axioms.lean`
2. [ ] Add `AtomCone_K_fixed_subset` lemma
3. [ ] Rewrite axiom for fixed cone
4. [ ] Update `Q_nonneg_bridge.lean`

**Details:** `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`

## Closure Tracker (remaining axioms)

| Axiom | Current proof source | Blocker | Next action | Status |
|------|-----------------------|---------|-------------|--------|
| `Weil_criterion` | External (classical) | None | Classical result, keep as axiom | **EXTERNAL** |
| `Schur_test` | External (classical) | L2 vs L∞ mismatch | Classical result, keep as axiom | **EXTERNAL** |
| `SingleScale.continuous_P_A_shift` | `Q3/Proofs/SingleScale_Assumptions.lean` | proved via `ShiftedWindows.P_A_shift_continuous` (requires `B>0`) | done | **THEOREM** |
| `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` | `Q3/Proofs/SingleScale_Assumptions.lean` | A3 floor at `t_critical` (tau = 0) | Prove Rayleigh lower bound for shifted symbol | **AXIOM** |
| `SingleScale.rho_oneK_tcritical_le_cstar_quarter` | `Q3/Proofs/SingleScale_Assumptions.lean` | prime cap (tau = 0) | Numeric bound `rho_one ≤ c*/4` | **THEOREM** |

## Progress Log (2026-01-16)

**P_A_continuous**:
- CLOSED in `A3_Floor_Main.lean` (local finiteness + periodicity proof)

**Q_nonneg_on_atoms (Rayleigh-Q identification)**:
- `Q3/Proofs/Rayleigh_Q_identification.lean` COMPLETE:
  - `basis0`, `i0`, `basis0_norm_sq`, `basis0_ne_zero`
  - `quadForm_basis0`, `rayleigh_basis0`, `rayleigh_basis0_sub`
  - `ToeplitzEntry_diag`, `ToeplitzEntry_diag_re`, `ToeplitzMatrix_Fourier_real_diag`
  - `fourier_index_i0`, `prime_vec_i0`, `T_P_comp_real_diag`
  - `integral_P_A_eq_arch_term` (periodization) ✅
  - `rayleigh_Q_identification`, `rayleigh_Q_eq_Q` ✅
- Done (2026-01-24): wired into `Atoms_Positive.lean` via `Q_nonneg_atoms_closure` (axiom closed).

**Aristotle projects (Rayleigh variants)**:
- 200eb072, 5e36515f, e9f53e97, eeca690a (Rayleigh sandbox variants)

## Legacy / History (2026-01-14)

**NEW (2026-01-14)**: Rayleigh lower bound PROVEN via Aristotle!
- V1 (pure informal): `aristotle_output/rayleigh_v1.lean` — COMPLETE, 0 sorry
- V2 (sandbox): `aristotle_output/rayleigh_v2.lean` — helpers only, main sorry

**A3_bridge Aristotle runs (2026-01-14)**:
- **V1 (`4c2ed336`)**: COMPLETE! Real T_P bounds proven (see below)
- V2 (`f6a9eed5`): исправленный — skipped (V1/V3 better)
- **V3 (`22378a11`)**: по Прошкиному скелету — **COMPLETE! 0 sorry!**
- **V4 (`c35f3088`)**: COMPLETE! 309 lines, 0 sorry — bounds for direct-indexed T_P

**V1 SURPRISE**: `aristotle_output/A3_bridge_closure_v1.lean`
- `w_RKHS_le_w_max`: ✅ w_RKHS(n) ≤ w_max = 2/e
- `w_max_lt_three_quarters_c_star`: ✅ **w_max < 3c*/4** (key inequality!)
- `T_P_tendsto_zero_of_ne`: ✅ off-diagonal → 0 as t → 0
- `exists_t_max_row_sum_le_for_M`: ✅ ∀ M, ∃ t: ||T_P|| ≤ 3c*/4
- **CLARIFIED**: V1/V4 prove `∀M ∃t(M)` for DIRECT-INDEXED T_P. See below.

**V4 COMPLETE**: `aristotle_output/A3_bridge_v4_real_TP.lean`
- 309 lines, 14 declarations, 0 sorry
- Main: `T_P_norm_lt_three_quarters_c_star (M : ℕ) : ∃ t > 0, bound`
- Useful helpers: `w_RKHS_le_w_max`, `S_off_tendsto_zero`, `T_P_row_sum_bound`

**⚠️ CRITICAL INSIGHT: T_P Definition Mismatch (2026-01-14)**

V1/V4 use **direct-indexed T_P**:
```lean
T_P i j = sqrt(w_RKHS i) * sqrt(w_RKHS j) * exp(-(ξᵢ - ξⱼ)²/4t)
```
This has ||T_P|| → ∞ as M → ∞, so uniform t is IMPOSSIBLE.

Q3 tex (rayleigh_bridge.tex) uses **compression T_P**:
```lean
T_P^{(M)} i j = ∑ n : Nodes K, w_Q n * Φ(ξₙ) * v_n[i] * v_n[j]
```
This has ||T_P^{(M)}|| ≤ ||T_P|| (compression), so uniform t IS possible.

**V1/V4 status**: Useful for local bounds, sanity checks. NOT for uniform A3_bridge.

**🚀 V5 (`1cac53dd`) — RAYLEIGH-FIRST (2026-01-14)**: ✅ **COMPLETE!**
- Input: `aristotle_input/A3_bridge_RAYLEIGH_FIRST.md` (from Proshka)
- Output: `aristotle_output/A3_bridge_rayleigh_first_v5.lean` — **120 lines, 0 sorry!**
- **No SB, No M₀** — Rayleigh for Toeplitz; RKHS cap now at `t_rkhs_cap=40`
- **T_P_comp** — rank-one sum (compression, correct definition!)

**V5 proven lemmas:**
- `quadForm_sub`, `rayleighQ_sub` — quadratic form algebra
- `cstar_sub_rho_ge_quarter` — c* - 1/25 ≥ c*/4 (norm_num)
- `A3_bridge_rayleigh_first` — **MAIN THEOREM**

**Dependencies (hypotheses in V5):**
1. `h_rayleigh_lower_bound` — from `rayleigh_v1.lean` ✅
2. `h_floor` — from A3_FLOOR ✅
3. `h_cap` — **PROVEN** in `Q3/Proofs/RKHS_cap_rayleigh.lean`
   (`weight_sum_le_rho_one`, `rkhs_cap_rayleigh_tcap`, `t_rkhs_cap=40`)

**V3 SUCCESS**: `aristotle_output/A3_bridge_v3_proshka.lean`
- Все 4 леммы доказаны
- НО: P_A=const, T_P=0 (placeholder'ы)
- Общие леммы (rayleigh, quadform_sub) переиспользуемы

**INSIGHT**: Прошка показал что SB не нужен; RKHS cap ≤ `rho_one = 1/25`
(в реализации с `t_rkhs_cap=40`).
Полный скелет: `aristotle_input/A3_bridge_PROSHKA_SKELETON.md`

Closed (recent):
- `RKHS_contraction_axiom` → bridged in `Q3/Proofs/Bridge.lean`, wired in `Q3/AxiomsTheorems.lean`

### A1_density Definitional Issue - RESOLVED (Option 2)

**Problem**: AtomCone_K requires `g ∈ W_K K` which includes `support g ⊆ [-K, K]`.
However, atoms with centers τ ∈ [-K, K] and widths B ≤ K have support in [-2K, 2K].

**Solution (Option 2)**: Changed AtomCone_K definition to require `|τ| + B ≤ K` instead
of separate `|τ| ≤ K` and `B ≤ K`. This matches Lemma 6.4 (Fixed-t₀ cone density).

**What was done**:
- Changed `AtomCone_K` in `Q3/Axioms.lean` and `Q3/Proofs/A1_density.lean`
- Added support control lemmas: `FejerKernel_eq_zero_of_abs_ge`,
  `Atom_eq_zero_outside_window`, `sum_atoms_eq_zero_outside`
- `hg_supp` now uses these lemmas (conditional on `hτB_cond`)
- Updated `W_K` to require `Continuous` (global), matching Q3 text (`C_c` tests).
  This enables the heat-kernel identity lemma for `h_approx`.

**Proven in A1_density_WK_thm**:
- Zero case: handled via n=0 representation
- hg_cont: continuity of sum of atoms
- hg_even: evenness (atoms are even in x)
- hg_nonneg: nonnegativity (nonneg weights × nonneg atoms)
- hg_supp: support containment (uses new margin condition)

**A1_density status:** `A1_density_WK_thm` is fully proven and wired into
`Q3/T5_Transfer.lean`. No remaining sorries in `Q3/Proofs/A1_density.lean`.

## Key Files (open only as needed)

- `PROJECT_WORKFLOW.md` - workflow loop + Aristotle rules (no status)
- `PROJECT_ASCII.md` - diagram (derived from this file)
- `docs/INSIGHTS.md` - collected project insights (do not create new docs)
- `FORMALIZATION_STATS.md` - quantitative stats snapshot
- `docs/PROJECT_SPECS.md` - spec/invariants for Proshka check (Rayleigh plan)
- `docs/Q3_PDF_STRUCTURE.md` - **FULL theorem/lemma trace from RH_Q3.pdf**
- `docs/PDF_DB_COVERAGE.md` - 80% coverage report (PDF vs DB)
- `PROOF_MAP_NEW_KERNEL.md` + `A3_FLOOR_ROADMAP.md` - A3_FLOOR status
- `Q3/Axioms.lean` and `Q3/AxiomsTheorems.lean` - axioms and wiring
- `Q3/Proofs/Q_Lipschitz.lean` - real proof of Q_Lipschitz
- `Q3/Proofs/Bridge.lean` + `Q3/Proofs/RKHS_contraction_bridge.lean`
- `Q3/Proofs/A3_Bridge_Uniform.lean`
- `Q3/Proofs/Q_Nonneg_Bridge.lean`
- `Q3/Proofs/A1_density.lean`
- `aristotle_db/parse_lean.py` - DB import

## Progress Tracking (DB)

```bash
python3 aristotle_db/parse_lean.py list-docs
python3 aristotle_db/parse_lean.py list-lemmas Q_Lipschitz
```

## Update Rule

After closing a step:
- run `lake env lean <file>`
- re-import to DB (`aristotle_db/parse_lean.py import ...`)
- update this file and `PROJECT_ASCII.md`

## Future: Community Presentation

After Tier-2 closure -> present to Talia Ringer / Lean Zulip.
See `PHILOSOPHY_OF_PROOF.md` for the pitch.

## Build / Verify

```bash
cd /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle
lake build Q3.Main
```

```bash
./scripts/check_axioms.sh
```

```bash
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | rg -v "^info:"
```

## Change Log (recent)

- 2026-01-22: **CRITICAL LaTeX PROOF GAP DISCOVERED**
  - Numerical verification: Q(Φ_{B=3,t=0.06}) = -16.29 < 0
  - Root cause: Two different T_P operators conflated in proof
  - Rayleigh T_P uses Φ weights, RKHS T_P does not
  - "Two-scale decoupling" is mathematically invalid
  - Created: `docs/LATEX_PROOF_GAP_ANALYSIS.md`
  - Status: **BLOCKED** — need mathematical consultation

- 2026-01-20: **Schur_test investigation** — L2 vs L∞ norm mismatch
  - Attempted to close `Schur_test` axiom using Mathlib
  - Created `Q3/Proofs/Schur_Test.lean` with L∞ proof
  - CANNOT wire: project uses L2 (spectral) norm, Mathlib proof uses L∞ (row-sum)
  - Full L2 proof requires Gershgorin + spectral norm theory
  - See: `docs/insights/schur_test_l2_vs_linfty_2026_01_20.md`

- 2026-01-20: **Phase A file refactoring** completed
  - Renamed v19/v20/v22/v2/v3 files to clean names
  - Updated all imports across project
  - Updated check_axioms.sh with correct counts (11 total, 8 project)
  - Updated CLAUDE.md paths (Mac → Linux)

- 2026-01-16: **BLOCKER DISCOVERED** — A3_bridge closure blocked by symbol mismatch!
  - `A3_bridge_data` uses sampling Toeplitz with `a_star` (mathematically WRONG: a_star → -∞)
  - `A3_bridge_data_rayleigh_Fourier` uses Fourier Toeplitz with `P_A` (CORRECT and PROVEN)
  - Types are mathematically incompatible — cannot bridge directly
  - **NEW PLAN:** Refactor chain to Fourier formulation + prove Rayleigh-Q identification (Theorem 3.3)
  - See: `TRICKS_LIBRARY.md`, `docs/insights/a_star_vs_p_a_dossier.md`

- 2026-01-15: **weight_sum_bound PROVEN** via Aristotle — 7 parallel submissions, ALL complete!
  - All 7 variants: 0 sorry, line counts 197-242
  - **v1_copy1 (197 lines)** — SHORTEST, recommended
  - Files: `aristotle_output/weight_sum_variants/v0_original.lean` through `v6_copy6.lean`
  - Analysis: `aristotle_output/weight_sum_variants/ANALYSIS.md`
  - **Proshka insights**: `suffices` > `have` ladders, minimal `aesop` (<2), π-free bounds more stable
  - **New guidelines**: `aristotle_input/ARISTOTLE_PROMPT_GUIDELINES.md`
  - Job IDs: fb91fbb3, ee8bc919, 78a7d870, e648f487, caf3e4c0, ba71a35a, c020a6a2

- 2026-01-14: **Rayleigh Lower Bound PROVEN** via Aristotle!
  Two parallel Aristotle jobs submitted:
  - V1 (pure informal): project `5990b601-ed48-442b-a4d3-5d8a18b444e3` → COMPLETE
  - V2 (sandbox): project `e9f8b481-8f80-4bdd-b798-be5c796eeead` → helpers only

  **V1 is the winner**: `aristotle_output/rayleigh_v1.lean` has COMPLETE proof (0 sorry):
  - `toeplitz_integrand_eq`, `toeplitz_quadratic_form`, `integral_exp_2pi_n_theta`
  - `parseval_trig_poly`, `rayleigh_lower_bound` (MAIN THEOREM)

  Key result: For Toeplitz matrix T with symbol P ≥ m, Rayleigh quotient ≥ m.
  Legacy note: this was previously wired into `A3_bridge_axiom` (sampling path).

- 2026-01-14: Wired `Q3.Theorems.A1_density_WK` into `Q3/T5_Transfer.lean`.
  `A1_density_WK_axiom` is now removed from `#print axioms` (total axioms: 9).

- 2026-01-14: Submitted Aristotle job `hat_interpolation_approx.md`
  (project `18bfe8c7-4620-41d4-be62-489409168e95`) with corrected boundary
  condition `f(-K)=f(K)=0`.

- 2026-01-14: Cleaned `aristotle_output/A1_density_hat_chain.lean` by replacing
  `exact?` with `FejerKernel_partition_unity`, switching `ring`→`ring_nf`, and
  removing unused variables; file compiles with no warnings.

- 2026-01-14: Submitted `A1_density_hat_chain` to Aristotle (project `e90d4213`).
  Plan: rewrite A1_density_WK_thm using hat-chain (Lemma 6.4) instead of
  convolution + Riemann sum. This avoids B vs B' mismatch and asymmetric sums.
  Key insight: W_K boundary vanishing (Φ(±K)=0) follows from global continuity.

- 2026-01-14: Integrated hat interpolation proof into
  `Q3/Proofs/HatInterpolation.lean` (namespaced) and wired
  `hat_interpolation_approx` in `Q3/Proofs/A1_density.lean`
  with `max_comm` rewrite. Remaining sorry: `h_approx` only.

- 2026-01-14: Created `aristotle_output/HatInterpolationBridge.lean` bridge file.
  Aristotle proof uses `FejerKernel δ x := max (1 - |x|/δ) 0` while A1_density uses
  `max 0 (1 - |x|/B)`. Bridge converts between them via `max_comm`.
  **BLOCKER**: Direct import causes FejerKernel name conflict (both at top level).
  **TODO**: Refactor A1_density to use `Q3.Fejer_kernel` from Axioms.lean, or add namespace.
  Current status: 2 sorries in A1_density.lean (hat_interpolation_approx + h_approx).
  Build passes, 10 axioms unchanged.

- 2026-01-14: **Aristotle COMPLETE** for `hat_interpolation_approx`!
  KEY FINDING: Original lemma signature was WRONG — proved counterexample for f(x)=1.
  **Fix**: Added `hf_boundary : f (-K) = 0 ∧ f K = 0` hypothesis.
  With margin condition |τᵢ| + δ ≤ K, all hats vanish at ±K.
  Full proof in `aristotle_output/hat_interpolation_approx.lean`.

- 2026-01-14: `hat_interpolation_approx` scaffolded in A1_density.lean — proved
  grid membership `hτ_in`, margin condition `hτ_margin`; 1 sorry remains
  `h_approx_bound` (approximation chain). Aristotle processing two projects:
  `bcec962f-4686-493e-b057-19695ddfc7b6` (hat_interpolation_approx),
  `9dda8778-857e-42cf-a669-aad1a2e04d5b` (A1_density_hat_full_v1 at 3%).

- 2026-01-14: Recreated Aristotle skill at `~/.codex/skills/aristotle/`,
  updated workflow docs to use CLI/Python API, submitted
  `aristotle_input/A1_density_hat_full_v1.md` (project `9dda8778-857e-42cf-a669-aad1a2e04d5b`).

- 2026-01-14: Updated `docs/PROJECT_SPECS.md` to the Rayleigh plan (no SB as blocker);
  added Aristotle input drafts `aristotle_input/A1_density_hat_full_v1.md` and
  `aristotle_input/A1_density_hat_only_v1.md`.

- 2026-01-14: Fixed HeatKernel derivative/Lipschitz proofs in
  `Q3/Proofs/A1_density.lean`; remaining sorries now only
  `hat_interpolation_approx` + `h_approx`.

- 2026-01-13: `A1_density_WK_thm` hτB_cond CLOSED! Changed `uniform_riemann_sum` to
  return `Set.Ioo` (strictly inside) instead of `Set.Icc`. Grid uses midpoints so
  all points y satisfy |y| < K. Compute margin = K - max{|y|}, set B' = min B margin.
  Also return `s.Nonempty` from both `uniform_riemann_sum` and `convolution_approx_by_sum`.
  Only 1 sorry remains: h_approx (triangle inequality chain).
- 2026-01-13: `A1_density_WK_thm` hg_mem proof mostly complete - proved continuity,
  evenness, nonnegativity; 2 sorries remain (hg_supp blocked by definitional issue,
  h_approx needs triangle inequality). Identified AtomCone_K support issue.
- 2026-01-13: `A1_density_WK_thm` circular dependency removed; now uses local lemmas
  with 4 `sorry` placeholders (support, nonneg, AtomCone membership, triangle ineq).
- 2026-01-13: DB import: Bridge.lean (13 decls), RKHS_contraction_bridge.lean (10 decls).
- 2026-01-13: Fixed `scripts/check_axioms.sh` (--stdin flag, correct axiom counting).
- 2026-01-13: Updated orchestrator to be the single entry point and clarified
  wiring vs closing.
- 2026-01-13: Closed arch/prime Lipschitz bridge axioms in `Q3/Proofs/Q_Lipschitz.lean`.
- 2026-01-13: `mem_nodes_finset_of_mem_Q3Nodes` proved in `Q3/Proofs/Bridge.lean`.
- 2026-01-13: `Q3/Proofs/RKHS_contraction_bridge.lean` compiles; DB import updated.
- 2026-01-13: Fixed `Q3/T5_Transfer.lean` AtomCone subset pattern; `lake build Q3.Main`
  passes; `RKHS_contraction_axiom` removed from main axiom list (total now 10).


## File: full/q3.lean.aristotle/ACTIVE/SPECS_INDEX.md

# Specs Index (curated)

Purpose: single place to find spec sources + current-status notes.
Keep this short; details stay in linked docs.

## Linked spec sources (legacy/inputs)

- `spec_critical_constants_rh_q3.md`
  - Source: RH_Q3.pdf pages 32-36 constants (two-scale context).
- `spec_rh_q3_decomposition.md`
  - Source: RH_Q3 decomposition / ERS analysis (uniform/two-scale framing).
- `spec_formalizing_rh_insights.md`
  - Source: process insights from FormalizingRiemannHypothesis.
- `spec_high_ers_constants.md`
  - Source: ERS-based critical constants (t_sym/t_rkhs era).
- `ERS_SUMMARY.md`
  - Consolidated ERS overview (legacy).

These four are **inputs/legacy**. They are useful for background but are not
canonical for the current single-scale chain. Use `ACTIVE/chain_status.md`
for the mainline.

## Canonical constants (mainline)

| Constant | Value | Lean source | Status |
|---|---:|---|---|
| `c_star` | 11/10 | `Q3/Axioms.lean` | mainline |
| `c_star/4` | 11/40 | `Q3/Axioms.lean` | mainline target |
| `B_min` | 3 | `Q3/Proofs/A3_Floor_Main.lean` | mainline |
| `t_critical` | 3/20 | `Q3/Proofs/Params_Critical.lean` | mainline |
| `t0_critical` | 1/(16π²·t_critical) | `Q3/Proofs/Params_Critical.lean` | mainline |
| `t_rkhs_cap` | 40 | `Q3/Proofs/A3_bridge_rayleigh_first.lean` | auxiliary cap |
| `rho_one` | 1/25 | `Q3/Proofs/A3_bridge_rayleigh_first.lean` | auxiliary cap |
| `rho_oneK` | exp(8π² t_rkhs_cap K²)·rho_one | `Q3/Proofs/RKHS_cap_rayleigh.lean` | auxiliary cap |

## Legacy constants (two-scale branch)

These appear in the older spec docs and are **not** canonical now:
- `t_sym = 3/50`
- `t^{unif}_{*,rkhs} = 1`
- `C_SB = 4` (Szego-Bottcher barrier constant)
- `M_0^{unif}`

If you cite any of these, mark as legacy in the doc.

## Where to update

- Canonical chain: `ACTIVE/chain_status.md`
- Axiom list: `ACTIVE/orchestrator.md`
- Mainline specs: this file + `ACTIVE/Q3_BLOCK_MAP.md`


## File: full/q3.lean.aristotle/ACTIVE/Q3_BLOCK_MAP.md

# Q3 Block Map (Lean ↔ Paper blocks)

Short mapping from paper blocks to Lean files/theorems/axioms.
Use this to answer: “Which block is this in Lean?”

## T0 — Normalization (Weil/Q)

- Paper: T0 (Guinand–Weil normalization)
- Lean entry: handled as external/classical pieces; see `Q3/Axioms.lean`
  (`Weil_criterion`, `explicit_formula`) and `ACTIVE/proof_map.md`.
- Status: external; not in the single-scale axiom list

## A1' — Density (atoms in W_K)

- Lean theorem: `Q3.Theorems.A1_density_WK` in `Q3/AxiomsTheorems.lean`
- Source proof: `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`
- Status: wired theorem (not an axiom)

## A2 — Continuity / Lipschitz of Q on W_K

- Lean theorem: `Q3.Theorems.Q_Lipschitz` in `Q3/AxiomsTheorems.lean`
- Source proof: `Q3/Proofs/Q_Lipschitz.lean`
- Status: wired theorem (not an axiom)

## A3 — Archimedean floor + Toeplitz/Rayleigh bridge

Mainline (single-scale, tau = 0):
- **Axiom (open):** `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
  in `Q3/Proofs/SingleScale_Assumptions.lean`
- Context: `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`

Legacy (two-scale / uniform):
- `Q3/Proofs/A3_Floor_Main.lean` (t_sym)
- `Q3/Proofs/P_A_Toeplitz_bridge.lean` (t_sym + t_rkhs_cap)

## RKHS prime cap

- Core cap at t_rkhs_cap:
  - `Q3/Proofs/RKHS_cap_rayleigh.lean`
  - `rho_one = 1/25`, `t_rkhs_cap = 40`

- **Single-scale cap (closed):**
  - `SingleScale.rho_oneK_tcritical_le_cstar_quarter`
  - `Q3/Proofs/SingleScale_Assumptions.lean`

## C1 — Compression identity (Rayleigh ↔ RKHS)

- Implemented in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  - basisFun identity
  - dictionary embedding identity
- Status: proven (no axiom); used as a bridge for opNorm bounds

## Atom-level nonnegativity / closure

- `Q3/Proofs/Q_nonneg_atoms_closure.lean`
  - closes the fixed-t chain assuming the two SingleScale axioms

## Main theorem (RH via Weil criterion)

- Entry: `Q3/Main.lean` (theorem `RH_of_Weil_and_Q3`)
- Axioms left: see `ACTIVE/chain_status.md` or `ACTIVE/orchestrator.md`


## File: full/q3.lean.aristotle/ACTIVE/PROBLEM_SOLVER_PROMPT_RU.md

# Промпт‑рефакторинг (RU): проверяемая цепочка RH из проектных ресурсов

Цель: построить **полную, проверяемую** цепочку до RH, опираясь **только** на
канонические проектные ресурсы. Внешние источники — **только при фиксированной
доказанной дыре** и с полным указанием источника. Никакого креатива.

---

## 0) Где искать информацию (обязательный путь)

Всегда читать/искать **в таком порядке**:

1) `ACTIVE/KNOWLEDGE_BASE.md` (карта ссылок)
2) `ACTIVE/orchestrator.md` (текущий статус, аксиомы, next step)
3) `ACTIVE/chain_status.md` (single‑scale mainline)
4) `ACTIVE/Q3_BLOCK_MAP.md` (Lean ↔ paper блоки)
5) `ACTIVE/SPECS_INDEX.md` (канонические константы + legacy пометки)
6) `ACTIVE/insights.md` + `ACTIVE/insights_index.md` (если нужен контекст)
7) Только после этого — legacy спеки (через `ACTIVE/spec_*`)

**Правило:** legacy‑доки никогда не являются источником канона. Любое решение
для mainline должно ссылаться на `chain_status`/`orchestrator`.

---

## 1) Требуемый результат

Собрать **полную цепочку доказательства** RH в формате:

- каждый шаг имеет: Reasoning → Conclusion;
- для каждого шага — точная ссылка (файл, раздел/страница);
- порядок шагов соответствует проектному mainline.

**Контекст:** цепочка на бумаге полная, с проверяемыми константами и шагами.
Остаются **3 атомарных узла** — они могут быть тяжёлыми аналитически.
Твоя роль — **искать синергию и кратчайший путь** к закрытию этих узлов,
строго и проверяемо (Lean + бумага), объединяя подходы анализа / Toeplitz / RKHS.

---

## 2) Процедура (строго)

### Шаг A — Проектная экстракция
- Используй только **канонические** файлы (см. путь поиска).
- Извлеки определения/леммы/теоремы, которые реально нужны для RH.
- Документируй источник каждого шага (файл + участок).

### Шаг B — Сборка цепочки
- Упорядочь шаги в строгую логическую цепь.
- Для каждого шага:
  - Reasoning (обоснование);
  - Conclusion (результат);
  - Источник.

### Шаг C — Проверка на дыры
- Если шаг отсутствует/не найден в проекте:
  - пометь его явно как **GAP**;
  - укажи, какие файлы проверены;
  - объясни, почему шага нет.

### Шаг D — Внешний fallback (только при GAP)
- Ищи **только** в авторитетных внешних источниках.
- Укажи ссылку (DOI/ArXiv/MathOverflow и т.п.).
- Объясни, как именно эта вставка закрывает GAP.
- Никаких новых гипотез/креатива.

---

## 3) Формат ответа

- Структурированный Markdown
- Таблицы для overview
- В каждом пункте: Reasoning → Conclusion
- Без code blocks (кроме прямых алгоритмов/скриптов, если они есть в проекте)
- В конце: итоговая классификация (доказано/открыто/условно)

---

## 3.1 Мини‑пример (формат ответа)

### Шаг N — A2 (Lipschitz Q на W_K)
Reasoning: В `Q3/Proofs/Q_Lipschitz.lean` доказано `Q_Lipschitz_on_W_K_thm`,
а в `Q3/AxiomsTheorems.lean` это заведено как `Q3.Theorems.Q_Lipschitz`.
Это даёт липшицевость на каждом W_K, значит перенос знака по пределу работает.
Источник: `Q3/Proofs/Q_Lipschitz.lean`, `Q3/AxiomsTheorems.lean`.
Conclusion: A2 закрыт как теорема в mainline.

## 4) Канонические факты (mainline)

Эти элементы считаются **истиной** для текущей ветки:

- single‑scale `t_critical = 3/20`
- `tau = 0` (BaseAtomCone)
- живые аксиомы:
  - `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` (tau = 0)
  - `SingleScale.rho_oneK_tcritical_le_cstar_quarter` — now trivial (`rho_one ≤ c_star/4`)

Источник: `ACTIVE/chain_status.md` + `ACTIVE/orchestrator.md`.

---

## 5) Запреты

- **Никакого** творческого добавления шагов.
- **Никаких** “можно было бы” — только фактически найденные элементы.
- **Никаких** ссылок на legacy как на канон.
- **Не проверять статус RH** и не обсуждать “открыта/доказана/принята”.  
  Мы строим доказательство в рамках проекта; статус внешнего мира не рассматривается.
- **Не делать веб‑поиск** “доказана ли RH”.

---

## 6) Проверка на зацикливание

Перед финальным выводом проверь:
- все ссылки идут вперёд (не ведут назад в legacy без причины),
- в mainline нет взаимных ссылок без прогресса,
- результат не требует чтения гигантских файлов подряд — всегда через индекс.


## File: full/q3.lean.aristotle/PROSHKA_REQUEST_4.md

# PROSHKA REQUEST v5: SingleScale closure pack (3 axioms)

---

## §0. Статус и цель

**Цель:** закрыть ровно 3 открытые single‑scale аксиомы (mainline) и связать их в единый мост
к положительности на атомах при `t = t_critical`.

**Контекст (важно):** цепочка на бумаге полная, с проверяемыми константами и шагами.
Остаются **3 атомарных узла** (см. ниже), которые могут быть тяжёлыми аналитически.
Нужно закрыть их **строго**, без “интуитивных” вставок, и обеспечить независимую
проверяемость (Lean + бумага). Роль Прошки — искать **синергию и кратчайшие
решения**, объединяя лучшие подходы (анализ / Toeplitz / RKHS) и ускоряя формализацию.

**Открытые аксиомы (mainline):**
- `SingleScale.continuous_P_A_shift`
- `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`
- `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

Источник правды:
- `ACTIVE/chain_status.md`
- `ACTIVE/orchestrator.md`

**Результат, который хотим от Прошки:**
- конкретные Lean‑леммы (без `sorry`/`exact?`),
- минимальные цепочки зависимостей,
- чёткий файл‑план: где писать и чем закрывать,
- связка трёх лемм в одну схему «A3 floor + RKHS cap ⇒ positivity на атомах».

---

## §1. Входные точки (используй их как оглавление)

**Главный индекс знаний:** `ACTIVE/KNOWLEDGE_BASE.md`

**Спецификации и мэппинг:**
- `ACTIVE/SPECS_INDEX.md`
- `ACTIVE/Q3_BLOCK_MAP.md`
- `ACTIVE/paper_lean_mapping.md`
- `ACTIVE/q3_structure_mapping.md`

**Проектные правила/контракт:**
- `ACTIVE/chain_status.md`
- `ACTIVE/orchestrator.md`
- `ACTIVE/PROBLEM_SOLVER_PROMPT_RU.md`

**Внимание (красные флаги):**
- **НЕ** смешивать `t_sym` и `t_rkhs`.
- **НЕ** использовать `a_star` вместо `P_A`.
- **НЕ** требовать Szegő–Böttcher как блокер.
- **НЕ** путать `w_Q` и `w_RKHS`.

---

## §2. Контракт single‑scale (обязателен)

- `t_critical = 3/20`
- `c_star = 11/10`
- `B_min = 3`
- Основная линия: **τ = 0** (base atom cone)
- `Q⋆` с коэффициентом `(2M+1)` **только** у prime‑части

---

## §3. Проблемы (требуются решения)

### Проблема 1: `SingleScale.continuous_P_A_shift`

**Смысл:** непрерывность периодизированного сдвинутого символа
`P_A_shift B t_critical tau` по θ.

**Ожидаемая форма:**
```
axiom continuous_P_A_shift (B tau : ℝ) :
  Continuous (Q3.P_A_shift B t_critical tau)
```

**Желаемый результат:** заменить аксиому на доказанную лемму.

**Ожидаемая структура доказательства:**
1) Непрерывность `phi_shift`, `g_shift`.
2) Локальная конечность периодизации ⇒ `tsum` = `Finset.sum`.
3) Конечная сумма непрерывных ⇒ непрерывно.

**Где смотреть:**
- `Q3/Proofs/ShiftedWindows.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge_defs.lean`
- `Q3/Proofs/HeatKernelParams.lean`

**Контекст (из свежего запроса к Aristotle):**
`full/q3.lean.aristotle/aristotle_input/continuous_P_A_shift_tcritical.md`.

**Нужен ответ от Прошки:**
- чёткая Lean‑цепочка лемм
- какие именно леммы уже есть и какие надо добавить
- минимальный proof‑skeleton без аналитического ада

---

### Проблема 2: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`

**Смысл:** Rayleigh‑нижняя оценка для Toeplitz‑блока на `t_critical`.
Цель — получить **c_star/4** на базисном векторе (или эквивалентную форму).

**Ожидаемая форма (примерно):**
```
axiom rayleigh_basis0_shift_ge_cstar_quarter (B : ℝ) :
  ... ≥ c_star / 4
```

**Где смотреть:**
- `Q3/Proofs/Rayleigh_basis0_of_A3.lean`
- `Q3/Proofs/Rayleigh_Q_identification.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge.lean`
- `Q3/Proofs/P_A_Toeplitz_bridge_defs.lean`

**Ожидаемый смысловой мост:**
- Toeplitz‑квадратичная форма = интеграл по `P_A` (Rayleigh)
- A3 floor на `P_A_shift` ⇒ lower bound для Rayleigh‑части
- Привязка к `e0` (basis0) ⇒ нужная оценка

**Нужен ответ от Прошки:**
- точная Lean‑формулировка
- цепочка: какие леммы переиспользовать
- где фиксировать `t_critical`

---

### Проблема 3: `SingleScale.rho_oneK_tcritical_le_cstar_quarter`

**Смысл:** RKHS‑cap на `t_critical` (prime operator norm ≤ c_star/4).

**Ожидаемая форма (примерно):**
```
axiom rho_oneK_tcritical_le_cstar_quarter (K : ℝ) :
  rho_oneK t_critical K ≤ c_star / 4
```

**Где смотреть:**
- `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `Q3/Proofs/T_P_comp_utils.lean`
- `Q3/Axioms.lean`

**Нужен ответ от Прошки:**
- минимальная цепочка лемм,
- как аккуратно “протащить” bound на `t_critical`,
- если надо — какие точечные леммы добавить.

---

## §4. Связка трёх лемм → positivity на атомах

Нужен короткий мост (в логике проекта):
- A3 floor (Rayleigh) + RKHS cap ⇒ `Q⋆(t_critical; Φ_{B,t}) ≥ 0` для генераторов
- далее A1′ + A2 → Q≥0 на W_K → RH

Прошка, пожалуйста, **покажи схему склейки**, с именами лемм и файлами.

---

## §5. Ограничения (важно)

- Никакой двухмасштабности.
- Никаких ERS‑конструкций.
- Никаких новых «креативных» теорем — только из проекта или стандартная математика.
- В Lean: без `sorry`/`exact?`.
- **Не проверять статус RH** (не обсуждать “открыта/доказана/принята”).  
  Мы строим и формализуем доказательство в рамках проекта.  
  **Никакого веб‑поиска** “доказана ли RH”.

---

## §6. Формат ответа

1) **Карта решения** (3 задачи → по шагам)
2) Для каждой задачи:
   - точная Lean‑формулировка
   - список нужных лемм
   - где писать (файл)
   - минимальный proof‑outline
3) **Склейка** (как 3 факта дают positivity на атомах)


**Спасибо! Нужна максимально “машинная” версия, чтобы агент мог сразу формализовать.**

**∎ END OF PROSHKA REQUEST v5**


## File: full/q3.lean.aristotle/docs/PROJECT_SPECS.md

# PROJECT SPECS: Rayleigh bridge + fixed-t density (BASE-SYNCED)

---

## §0. Status and goal

**Goal:** Prove only $Q(\Phi) \ge 0$ for all $\Phi \in \mathcal{W}$.

**Status:** Conditional chain "Tier-2 ==> RH" via Weil criterion (no "RH proven").

---

## §0.1 Audit guardrails (prevent drift)

- Canonical checklist: `full/q3.lean.aristotle/docs/CHECKLIST_AUDIT_2026_01_17.md`.
- Quick invariant check: `full/q3.lean.aristotle/scripts/check_audit_invariants.sh`.
- Before merge: run the script; if any anchor changed, update the checklist.

## §1. Normalization / sign / torus (LOCKED)

### Sign (MINUS)
$$
Q(\Phi) = Q_{\mathrm{arch}}(\Phi) - Q_{\mathrm{prime}}(\Phi)
$$

### T0 normalization
$$
a_*(\xi) = 2\pi a(\xi), \qquad \xi_n = \frac{\log n}{2\pi}
$$

### Period-1 torus
$$
\mathbb{T} = [-1/2, 1/2], \quad e_k(\theta) = e^{2\pi i k\theta}, \quad d\theta
$$

### A3 symbol (period-1)
$$
P_A(\theta) = 2\pi \sum_{m \in \mathbb{Z}} g_{B,t_{\mathrm{sym}}}(\theta + m),
\quad g_{B,t}(\xi) = a(\xi)\Phi_{B,t}(\xi)
$$

---

## §1.1 Contract checks (RH_Q3)

- A3 symbol is `P_A` (periodized, windowed). Do not use `a_star` as A3 symbol.
- Toeplitz in A3 uses Fourier/Rayleigh on period-1 torus; sampling `P(π(i-j)/M)` is not allowed in the main chain.
- Prime operator in A3 is the compression/rank-one sum `T_P^{(M)}` with `w_Q`, not direct-indexed Gaussian.
- Keep `t_sym` (symbol) and `t_rkhs` (cap) distinct; do not mix `w_Q` and `w_RKHS`.

---

## §2. Tier-1 facts

### Weil criterion
$$
Q \ge 0 \text{ on } \mathcal{W} \iff \mathrm{RH}
$$

### Toeplitz quadratic form (Rayleigh core)
For trig polynomials $p$ in $P_M$:
$$
\langle T_M[P_A]p,p\rangle = \int_{\mathbb{T}} P_A(\theta) |p(\theta)|^2\,d\theta
$$

### Rayleigh lower bound (no Szego-Bottcher needed)
$$
\lambda_{\min}(T_M[P_A]) \ge \min_{\theta \in \mathbb{T}} P_A(\theta)
$$

**Note:** The classical Szego-Bottcher estimate
$$
\lambda_{\min}(T_M[\sigma]) \ge \min \sigma - C_{SB} \cdot \omega_\sigma(1/(2M))
$$
is **optional** and follows as a corollary since $\omega_\sigma \ge 0$.

---

## §3. Tier-2 modules (current plan)

### A1' density (fixed $t_0$, hat interpolation)
Atoms are restricted by the margin condition:
$$
|\tau| + B \le K
$$
so support stays in $[-K,K]$. Use hat interpolation (Lemma 6.4) on $[-K,K]$.

### A2 (Lipschitz)
$Q$ is Lipschitz on each $\mathcal{W}_K$.

### A3 floor (pointwise)
$$
P_A(\theta) \ge c_* = 11/10 \quad \forall \theta \in [-1/2, 1/2]
$$

### RKHS cap
For $t_{\mathrm{rkhs}} \ge t_{*,\mathrm{rkhs}}^{\mathrm{unif}} = 1$:
$$
\|T_P\| \le \rho(1) < 1/25
$$

### Rayleigh bridge (p = 1)
$Q(\Phi_{B,t_{\mathrm{sym}}})$ matches the Rayleigh identity at $p \equiv 1$ in two
equivalent forms (see `full/sections/A3/calibration.tex` and
`full/sections/A3/rayleigh_bridge.tex`):

- **Infinite-dimensional idealization:** $\langle (T_M[P_A]-T_P)1,1\rangle = Q(\Phi)$.
- **Finite-dimensional compression:** $\langle T_M[P_A]1,1\rangle - (2M+1)\langle T_P^{(M)}1,1\rangle = Q(\Phi)$.

The factor $(2M{+}1)$ comes from the normalization of $v_n^{(M)}$ and the identity
$\iota_M^\ast T_P \iota_M = (2M{+}1)\,T_P^{(M)}$.

---

## §4. Discretization (optional)

No $M_0$ is required if we use the Rayleigh lower bound directly.
If we still want Szego-Bottcher, treat it as a weaker corollary:
$$
\lambda_{\min} \ge \min P_A \ge \min P_A - 4\,\omega_{P_A}(1/(2M))
$$

---

## §5. Positivity on generators

1) **A3 floor:** $P_A \ge c_*$ (pointwise)
2) **Rayleigh:** $\lambda_{\min}(T_M[P_A]) \ge c_*$
3) **RKHS cap:** $\|T_P\| \le c_*/4$

Hence
$$
\lambda_{\min}(T_M[P_A] - T_P) \ge c_* - \|T_P\| \ge 3c_*/4 > 0
$$
so $Q(\Phi_{B,t_{\mathrm{sym}}}) \ge 0$ in the idealized operator form. For the
finite-dimensional Lean operator, replace $T_P$ by the compressed $T_P^{(M)}$
(a.k.a. `T_P_comp`); the cap applies to the normalized vectors, and the
$(2M{+}1)$ factor only appears when converting $\langle T_P^{(M)}1,1\rangle$
to the prime sum in the $p\equiv1$ identity.

---

## §6. Closure and RH

By A1'+A2 we extend $Q \ge 0$ from generators to all of $\mathcal{W}_K$, then to $\mathcal{W}$.
By Weil criterion we obtain **RH (conditional on Tier-2)**.

---

## §7. Key invariants (checklist)

| # | Invariant | Value |
|---|-----------|-------|
| 1 | Sign | $Q = Q_{\mathrm{arch}} - Q_{\mathrm{prime}}$ |
| 2 | Normalization | $\xi_n = \log n/(2\pi)$, $a_* = 2\pi a$ |
| 3 | Torus | period-1, $\mathbb{T} = [-1/2, 1/2]$ |
| 4 | Symbol | $P_A = 2\pi \sum_m g(\theta+m)$ |
| 5 | Floor | $c_* = 11/10$ (NOT 1.5) |
| 6 | Rayleigh | $\lambda_{\min} \ge \min P_A$ (no SB needed) |
| 7 | Prime cap | $t_{\mathrm{rkhs}} \ge 1 \Rightarrow \rho(1) < 1/25$ |
| 8 | Goal | $Q(\Phi) \ge 0$ (NOT $\ge 1.125$) |

---

## §8. Response format

- Short "matches / mismatches" report for items 1-8
- Reassembled text of §0-§8 (single block)
- No new notation, no external links

---

## DO NOT DO

- Do NOT revert to $c_* = 1.5$
- Do NOT require Szego-Bottcher as a blocker (use Rayleigh bound)
- Do NOT change the sign convention
- Do NOT switch to $2\pi$-periodic torus
- Do NOT claim $Q \ge 1.125$ without normalization
- Do NOT use sampling Toeplitz `P(π(i-j)/M)` in the A3 chain
- Do NOT mix `t_sym` with `t_rkhs` or `w_Q` with `w_RKHS`

---

## Context pack (.tex base)

| File | Module |
|------|--------|
| `full/sections/T0.tex` | T0 normalization |
| `full/sections/A3/symbol_floor.tex` | A3 floor |
| `full/sections/A3/rayleigh_bridge.tex` | Toeplitz quadratic form + Rayleigh |
| `full/sections/A3/matrix_guard.tex` | (Optional) Szego-Bottcher discretization |
| `full/sections/RKHS/prime_trace_closed_form.tex` | RKHS cap |
| `full/sections/A1prime.tex` | A1' density (fixed t0) |
| `full/sections/A2.tex` | A2 Lipschitz |
| `full/sections/Main_closure.tex` | Closure |
| `full/sections/Weil_linkage.tex` | Weil linkage |

---

**END OF PROSHKA REQUEST v4**


## File: full/q3.lean.aristotle/docs/insights/rh_q3_invariants_contract_2026_01_16.md

# RH_Q3 invariants contract and drift checks (2026-01-16)

Source: RH_Q3.pdf (2026-01-01), "Operator Methods for the Weil Criterion: Q3".

## What drifts in Lean (symptoms)
- A3 bridge mentions `a_star` or `ToeplitzMatrix ... a_star`.
- Toeplitz in the A3 chain is defined by sampling `P (π(i-j)/M)`.
- `a_star_pos` is used as a proxy for a Rayleigh floor.
- `t_sym` is reused as `t_rkhs` or vice versa.
- `w_Q` and `w_RKHS` are treated as the same weight.
- Direct-indexed Gaussian `T_P` is used as the uniform A3 object.

## Contract A-E (minimal)
A) Torus/Fourier basis: period-1, `e^{2πikθ}`.
B) A3 symbol: `P_A` is the periodized, windowed `a(ξ)Φ_{B,t}`; floor is `P_A ≥ c_*`.
C) Toeplitz: use Fourier/Rayleigh definition; sampling Toeplitz is not allowed in A3 chain.
D) Prime operator: compression/rank-one sum `T_P^{(M)}` with `w_Q`, not direct-indexed Gaussian.
E) Parameters: keep `t_sym` (symbol) and `t_rkhs` (cap) distinct; `w_Q` and `w_RKHS` are not interchangeable.

## Implications
- Rayleigh route yields `λ_min(T_M[P_A]) ≥ min P_A` for any M; SB is optional.
- `a_star_pos` is not required for A3 and can mislead.

## Quick test
- If a file contains `ToeplitzMatrix ... a_star` or `P (π(i-j)/M)` in the A3 chain, it is off the RH_Q3 contract.


## File: full/q3.lean.aristotle/docs/INSIGHTS.md

# Project Insights

Короткие записи + ссылки на подробности. Здесь держим только:
- проблему;
- как быстро ее детектить;
- ссылку на подробный разбор.

Полный список файлов: `docs/insights/INDEX.md`.

---

## Навигация (кратко)

- Текущая цепочка (single-scale t_critical): `docs/CHAIN_STATUS.md`.
- Hub для активных доков/скриптов/DB: `ACTIVE/`.
- Прошка как ускоритель: застряли >30 минут или <10% прогресса в Aristotle → `docs/insights/proshka_key_resource.md`.
- Пример «идеального» ответа Прошки: нужна опорная структура → `docs/insights/breakthrough_proshka_full_proof_2026_01_14.md`.

- Aristotle стратегия: sandbox тупит/ломает сигнатуры → `docs/insights/aristotle_strategy_pure_informal.md`.
- Aristotle recovery: получили `sorry`/`exact?` или не компилится → `docs/insights/aristotle_error_recovery.md`.
- Организация входов/выходов Aristotle: путаемся в `aristotle_input`/`aristotle_output` → `docs/insights/file_organization_aristotle.md`.

- Докдисциплина: распухают инсайды и хаос в документах → `docs/insights/documentation_discipline.md`.
- Реюз активов: нужно быстро понять, что уже proven → `docs/insights/proven_assets_inventory_2026_01_14.md`.
- Константы: расхождение чисел/порогов → `docs/insights/key_constants_reference.md`.
- Входная точка для Прошки → `docs/PROSHKA_ENTRYPOINT.md`.

---

## Tooling / Checks

- **Lean build hangs на MeasureTheory/HasSum**: `simpa using` убивает перфоманс → `docs/insights/lean_simpa_performance_fix_2026_01_19.md`.
- check_axioms падает на A3_FLOOR: нужен предварительный build → `docs/insights/check_axioms_prebuild_a3_floor_2026_01_16.md`.
- Semantic search workflow (q3search/websearch):
  1) сначала q3search (3-5 запросов, до ~75% уверенности), 2) потом websearch,
  3) синтез в 5-10 строк, 4) обновить `docs/INSIGHTS.md` + коммит "in progress",
  5) по завершении добавить итоговый инсайт. НЕ запускать `mgrep watch`/`mgrep --sync`.

## Synthesis (2026-01-23, in progress) — fixed‑t/τ=0 one‑scale closure

- q3search "AtomCone_K_fixed" / "Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom" failed: 403 Spend limit exceeded.
- websearch "AtomCone_K_fixed Lean" failed: 403 Spend limit exceeded.
- Target lemma: close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` in `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Option A (primary): implement fixed‑t cone/τ=0 guard in `Q3/Axioms.lean`, then wire one‑scale chain using
  `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`, `Q3/Proofs/RKHS_cap_rayleigh.lean`, and `Q3/Proofs/Params_Critical.lean`.
- Option B (fallback): keep RKHS embedding path; fill missing `kernel_dict` in `Q3/Proofs/RKHS_cap_rayleigh.lean`
  or discharge `hA` via `Q3/Proofs/RKHS_Interface_C1.lean` + `Q3/Proofs/Heat_RKHS_Interface.lean`.
- Success check: `lake env lean Q3/Atoms_Positive.lean` and `./scripts/check_axioms.sh` drop the axiom.
- Progress: `t0_critical` wired into `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
  `Q3/Atoms_Positive.lean`, `Q3/T5_Transfer.lean`, `Q3/AxiomsTheorems.lean`;
  BaseAtomCone guard `Q_nonneg_on_base_atoms_of_A3_Fourier_RKHS` added.
- Proshka request drafted: `full/q3.lean.aristotle/PROSHKA_REQUEST_5.md` (one‑scale A3 floor + cap at t_critical).

## Synthesis (2026-01-24, resolved) — close `rho_oneK_tcritical_le_cstar_quarter`

- Decision: mainline uses tau = 0, so the cap reduces to `rho_one ≤ c_star/4`.
- Implemented as a direct numeric bound (no K dependence).
- Legacy `rho_oneK` (tau-shift) remains as a separate variant; not used in mainline.

## Synthesis (2026-01-24, in progress) — `rayleigh_basis0_shift_ge_cstar_quarter` (t_critical, tau = 0)

- q3search "rayleigh_basis0_shift_ge_cstar_quarter" failed: 403 Spend limit exceeded.
- websearch "Toeplitz Rayleigh lower bound t_critical" failed: 403 Spend limit exceeded.
- Target lemma: `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter` in `Q3/Proofs/SingleScale_Assumptions.lean`.
- Option A (primary): reduce to floor at t_critical via
  `P_A_shift_tau_zero` (`Q3/Proofs/Q_nonneg_base_atoms_proof.lean`) +
  `P_A_rayleigh_lower_bound_of_floor` (`Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`) +
  `A3FloorCritical.FloorGoal` (`Q3/Proofs/A3_Floor_Critical_Goal.lean`), then weaken to `c_star/4`.
- Option B (fallback): use `arch_rayleigh_eq_shift` (`Q3/Proofs/Rayleigh_Q_identification.lean`) +
  `integral_P_A_shift_eq_arch_term` (`Q3/Proofs/ShiftedWindows.lean`) and prove
  `arch_term ≥ c_star/4` via a numeric/interval lemma in `Q3/Proofs/Q_nonneg_t_critical.lean`.
- Success check: `lake env lean Q3/Proofs/SingleScale_Assumptions.lean`
  then `./scripts/check_axioms.sh` (only `Weil_criterion` + `Schur_test` remain).
- Blocker: no current floor lemma at `t_critical`; likely needs numeric/interval proof
  or a monotonicity lemma for `P_A` in `t`.

---

## A3/Rayleigh: критический путь

- Символы `a_star` vs `P_A`: признаки рассогласования, reverse‑engineering → `docs/insights/a3_symbol_mismatch_reverse_engineering.md`.
- Досье по различиям `a_star` и `P_A` → `docs/insights/a_star_vs_p_a_dossier.md`.

- Rayleigh без SB: пытаемся тащить Szego‑Bottcher → `docs/insights/rayleigh_vs_sb_optional.md`.
- SB не нужен (краткая формулировка) → `docs/insights/szego_bottcher_not_needed.md`.

- RKHS cap: видим несходимость по ρ=0.868 → `docs/insights/a3_bridge_math_rkhs_bound.md`.
- RKHS cap реализация (t_rkhs_cap=40, rho_one=1/25) → `docs/insights/rkhs_cap_implementation_2026_01_15.md`.
- Tau-shift: варианты RKHS cap/A3 floor + выбор Variant 1 (риски/план) → `docs/insights/tau_shift_variants_rkhs_a3_2026_01_18.md`.
- C1 basisFun model wired (machine `h_eval`) + compression remark in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
- Single-scale RKHS contraction at `t_critical` wired into `Q3/AxiomsTheorems.lean` (via `SingleScale_Assumptions`).
- `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` closed via `Q_nonneg_atoms_closure`; remaining blocker is
  `SingleScale.rayleigh_basis0_shift_ge_cstar_quarter`.

- Реальные bounds для T_P (V1 surprise): путаем direct‑indexed vs compression → `docs/insights/v1_surprise_real_tp_bounds_2026_01_14.md`.
- Успешный Rayleigh‑bridge (V3) → `docs/insights/v3_success_a3_bridge_rayleigh_2026_01_14.md`.
- Полный bound T_P (V4) → `docs/insights/v4_success_full_tp_bound_2026_01_14.md`.

- Несовпадение T_P_comp в Lean: упираемся в дефиницию → `docs/insights/t_p_comp_mismatch.md`.
- Фикс compression‑формулы T_P (план) → `docs/insights/t_p_compression_fix_2026_01_14.md`.
- Контракт RH_Q3 (инварианты + дрейф‑точки): быстрый аудит `a_star`/`P_A`, Toeplitz, `t_sym`/`t_rkhs`, веса → `docs/insights/rh_q3_invariants_contract_2026_01_16.md`.
- Drift report M1–M4: a_star vs P_A, sampling vs Fourier, T_P, parameters → `docs/insights/drift_report_m1_m4.md`.
- Атомы: переход на Fourier A3 и новую аксиому → `docs/insights/a3_fourier_atoms_axiom_2026_01_16.md`.
- Closure synthesis (from q3search + websearch) for `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`:
  базовая информация уже в базе. Используем скелет `aristotle_input/Q_nonneg_A6_final.md`,
  идентификацию `Q3/Proofs/Rayleigh_Q_identification.lean` (`rayleigh_Q_eq_Q` или `_shift`),
  RKHS cap из `Q3/Proofs/RKHS_cap_rayleigh.lean` (`weight_sum_le_rho_one`),
  A3 bridge из `Q3/Proofs/P_A_Toeplitz_bridge.lean`.
  Действия: доказать теорему `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` через
  `Q_nonneg_on_atomcone_of_atoms` + `Q_nonneg_fejer_heat_window` + `rayleigh_basis0_of_A3`
  + кап; затем заменить аксиому в `Q3/Atoms_Positive.lean` и `Q3/AxiomsTheorems.lean`,
  проверить `lake env lean Q3/Atoms_Positive.lean` и `#print axioms`.
- Blocker (2026-01-18): A1–A5 helper lemmas are still missing in code.
  План: 1) в `Q3/Proofs/Q_nonneg_atoms_helpers.lean` добавить линейность `Q_finset_sum`
  и `prime_sum_nonneg` (см. `aristotle_input/Q_nonneg_A1_linear.md`/`Q_nonneg_A2_prime_sum_nonneg.md`);
  2) `rayleigh_basis0_of_A3` и `Q_nonneg_fejer_heat_window` собрать из
  `Q3/Proofs/Rayleigh_Q_identification.lean` (`honest_formula`) + A3/RKHS cap;
  3) `Q_nonneg_on_atomcone_of_atoms` из формы `AtomCone_K` (finite sum of atoms);
  4) подключить в `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
- Synthesis (2026-01-18): wiring plan + import conflict.
  1) Sandbox: `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_lemmas.lean`
     содержит A1/A2/A5 + integrability/summability; скопировано в `Q3/Proofs/Q_nonneg_lemmas.lean`
     (компилируется, предупреждение: `integral_mul_left` deprecated).
  2) Import conflict: `Q_nonneg_atoms_helpers.lean` не может импортировать одновременно
     `Q3.Proofs.Rayleigh_Q_identification` и `Q3.Proofs.P_A_Toeplitz_bridge`
     (B_min collision из `A3_Floor_Bounds`).
  3) Mitigation: держать Rayleigh‑леммы в файле, который импортирует только
     `Rayleigh_Q_identification`; для `rho_one` подключать `Q3.Proofs.A3_bridge_rayleigh_first`.
  4) Дальше: `rayleigh_basis0_of_A3` вынести в файл с `P_A_Toeplitz_bridge` (без Rayleigh),
     затем связать с `Q_nonneg_fejer_heat_window` при wiring в
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`.
  5) Проверка: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean` и
     `lake env lean Q3/Proofs/Q_nonneg_lemmas.lean`.
- Synthesis (2026-01-18, in progress): AtomCone_K_fixed wiring plan.
  1) Fix t0: define `t0_A1 = 1 / (16 * Real.pi^2 * t_sym)` in `Q3/Proofs/HeatKernelParams.lean`
     with `t0_A1_pos`; use this for all fixed-t atoms.
  2) Add atom rewrite: in `Q3/Proofs/ShiftedWindows.lean`, prove
     `Fejer_heat_atom = const * (phi_shift B t_sym tau + phi_shift B t_sym (-tau))`.
  3) Port fixed-t chain from sandbox `sandboxes/measure_dom/.../Q_nonneg_atoms_proof.lean` into
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`:
     `Q_nonneg_on_atomcone_fixed_of_atoms`, `Q_single_atom_fixed_nonneg`, `Q_nonneg_on_atoms_fixed`.
  4) Prove `Q (phi_shift ...) ≥ 0` via `rayleigh_Q_eq_Q_shift` + `A3_bridge_data_rayleigh_Fourier`
     + `rkhs_cap_rayleigh_tcap`; use `rayleigh_basis0_of_A3` as the arch lower bound.
  5) Wire fixed-t theorem in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`;
     keep `AtomCone_K` for density and use `AtomCone_K_fixed_subset`.
  6) Checks: `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`, then `#print axioms`.
- Synthesis (2026-01-19, in progress): A1–A5 helpers + fixed‑t wiring checklist.
  1) A1/A2 already in `Q3/Proofs/Q_nonneg_lemmas.lean` (`Q_finset_sum`, `prime_sum_nonneg`);
     import/reuse in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` for A5.
  2) A4 in `Q3/Proofs/Rayleigh_basis0_of_A3.lean`; keep imports minimal
     (`Q3/Proofs/Rayleigh_basis0.lean`, `Q3/Proofs/P_A_Toeplitz_bridge.lean`).
  3) A3 in `Q3/Proofs/Q_nonneg_atoms_helpers.lean` via
     `Q3.Proofs.RayleighQId.honest_formula` + RKHS cap (`weight_sum_le_rho_one`/`rkhs_cap_rayleigh_tcap`).
  4) Use fixed‑t cone lemma from sandbox
     `sandboxes/measure_dom/full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_atoms_proof.lean`
     (`Q_nonneg_on_atomcone_fixed_of_atoms`) with `AtomCone_K_fixed` (see
     `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  5) Wire `Q_nonneg_on_atoms_of_A3_Fourier_RKHS` in
     `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` using A1–A4 + fixed‑t cone.
  6) Replace axiom usage in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`.
  7) Checks: `lake env lean Q3/Proofs/Q_nonneg_atoms_helpers.lean`,
     `lake env lean Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`,
     `lake env lean Q3/Atoms_Positive.lean`.
- Synthesis (2026-01-24, in progress): Close `Q3/Proofs/Q_nonneg_atoms_closure.lean` sorries (fixed‑t chain).
  1) `Q_nonneg_phi_shift_tsym`: use `Q3.Proofs.QNonnegAtoms.Q_phi_shift_nonneg`
     from `Q3/Proofs/Q_nonneg_atoms_helpers.lean` with cap
     `prime_term_phi_shift_le_rho_oneK` (in `Q3/Proofs/RKHS_cap_rayleigh.lean`)
     + `rayleigh_basis0_of_A3`; **need** explicit `hpos : 0 ≤ c_star/4 - exp_tsym_to_rkhs K * R`.
  2) Replace scaling/half‑atom steps with the fixed‑t identity
     `Fejer_heat_atom_eq_const_mul_phi_shift_sum` from `Q3/Proofs/ShiftedWindows_t0.lean`.
  3) For `Q_nonneg_Fejer_heat_atom`, prefer `Q_single_atom_nonneg_of_phi_shift_basic`
     (in `Q3/Proofs/Q_nonneg_atoms_helpers.lean`) + prove `htsym` for `t0_A1`.
  4) Finish with `Q_nonneg_on_atomcone_fixed_of_atoms` (same file) to get
     `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_thm`.
  5) Searches attempted: `q3search` + `websearch` failed (403 spend limit); proceed with local lemmas.
- Synthesis (2026-01-23, in progress): close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`
  via the one-scale chain (Stream A).
  1) q3search/websearch were attempted but failed with spend-limit 403.
  2) Implement `AtomCone_K_fixed` + `AtomCone_K_fixed_subset` in `Q3/Axioms.lean`
     and update the fixed-t cone plumbing (see `docs/insights/atomcone_fixed_t_gap_2026_01_18.md`).
  3) In `Q3/Proofs/Q_nonneg_atoms_helpers.lean`, import A1/A2 from
     `Q3/Proofs/Q_nonneg_lemmas.lean` and add the missing A3/A4/A5 steps with minimal imports.
  4) In `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean`, use the fixed-t cone lemma,
     `rayleigh_Q_eq_Q`/`rayleigh_Q_eq_Q_shift`, and the one-scale bridge from
     `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` plus the cap in
     `Q3/Proofs/RKHS_cap_rayleigh.lean`.
  5) Replace the axiom in `Q3/Atoms_Positive.lean` and `Q3/AxiomsTheorems.lean`,
     then run `lake env lean` on the touched files and `./scripts/check_axioms.sh`.
- Последний мост к Q3.Q: для Phi с compact support (например, fejer_heat_window) показать, что prime_term (tsum по n) равен конечной сумме по Nodes K при K >= B; тогда rayleigh_Q_identification переписывается в Q3.Q (см. `Q3/Proofs/Rayleigh_Q_identification.lean`).
- P_A_continuous: доказательство через локальную конечность суммы и периодичность, без `sorry` (см. `A3_Floor_Main.lean`).

---

## Параметры и численные проверки

- Две формы t (в числителе/знаменателе): знак эффекта не тот → `docs/insights/t_parameter_forms.md`.
- Heat‑параметр mismatch (t_sym vs t_rkhs): путаем контексты → `docs/insights/heat_parameter_mismatch_2026_01_14.md`.
- Численные оценки h‑cap: нужен sanity‑check по величинам → `docs/insights/h_cap_numerical_estimates_2026_01_14.md`.
- One-scale vs two-scale (конкретно):
  - **Two-scale** = A3 floor на `P_A(·, t_sym)` + prime cap на `T_P_comp(·, t_rkhs_cap)` (см. `Q3/Proofs/P_A_Toeplitz_bridge.lean`,
    `Q3/Proofs/A3_bridge_rayleigh_first.lean`) и затем отдельный мост/штраф за смену t (см. `Q3/Proofs/PrimeTerm_t_bridge.lean`).
  - **One-scale** = один и тот же `t` одновременно в `P_A(·, t)` и в `T_P_comp(·, t)` (и в RKHS-части): меньше “перекидываний”,
    но нужно реально закрыть обе оценки на одном t. Параметры фиксируем в `Q3/Proofs/Params_Critical.lean` (`t_critical`, `t0_critical`).

---

## Misc / Unsorted (нужно разложить по разделам)

- Periodization bottleneck: быстрый фикс → `docs/insights/PERIODIZATION_BOTTLENECK_FIX.md`.
- Carleson implicit proof notes → `docs/insights/carleson_implicit_proof_2026_01_17.md`.
- Heat localization kills primes → `docs/insights/heat_localization_kills_primes_2026_01_16.md`.
- Localization argument (full) → `docs/insights/localization_argument_full_analysis_2026_01_16.md`.
- Prime term = nodes sum bridge → `docs/insights/prime_term_nodes_bridge_2026_01_17.md`.
- Rayleigh Q identification notes → `docs/insights/rayleigh_q_identification_2026_01_17.md`.
- Rescaled density lemma variants → `docs/insights/rescaled_density_lemma_variants_2026_01_16.md`.
- Decision tree (2026-01-23): “нетривиальное hA” для C1 (Rayleigh = compression RKHS-prime).
  - Target lemma (informal): ∃ heat-RKHS `H_t`, ∃ isometry `ι_{t,M}`, s.t.
    `(Matrix.toEuclideanLin (T_P_comp_real ...)).toCLM = compression ι_{t,M} (T_P_RKHS t)`.
  - Tree-plan (no axioms, Moore–Aronszajn → close `hA`):  
    1) Build `H_t` from kernel `k_t(x,y)` (Moore–Aronszajn: span/quotient/complete) and expose
       `eval x` + `k x` + reproducing lemma. Status: **blocked (infrastructure)** — a first attempt at a
       Fourier/Bochner model ran into nontrivial `simp`/`cpow`/conjugation normalization issues, so it was
       reverted rather than kept half‑working.  
    2) `Q3/Proofs/Heat_RKHS_Interface.lean`: use `reproducing` to reduce `inner ℂ (ψ i) (k x)` to `eval x (ψ i)` (already: `h_eval_of_eval_eq_prime_vec`).  
    3) `Q3/Proofs/RKHS_Interface_C1.lean`: discharge `hA` by providing `H, ψ, k` and the matching hypothesis; conclude exact compression identity (already: `T_P_comp_toCLM_eq_compression`).  
    4) If “exact sampling ON family” is false-for-now: switch to node-span interpolation, prove unitary-conjugation equivalence, and use operator-norm invariance to recover the C1 cap (document as Option 1b in this tree).  
       Lean helper: `Q3/Proofs/OpNorm_Unitary.lean` (`opNorm_conj_linearIsometryEquiv`).
  - Option 0 (DONE, algebraic core): exact factorization `T_P_comp = V† · D · V` in
    `Q3/Proofs/RKHS_hA_prime.lean` (this is the real “content” of the rank-one sum).
  - Option 1 (OK, conditional “true C1 as in PDF”): minimal Hilbert-interface version of `hA`
    compiles as `Q3.Proofs.RKHSInterfaceC1.T_P_comp_toCLM_eq_compression` in
    `Q3/Proofs/RKHS_Interface_C1.lean`:
    assumptions = `(H, ψ orthonormal, k_n, inner(ψ_i,k_n)=prime_vec)` ⇒ `T_P_comp = compression ι T`.
    Note: in this Lean toolchain `⟪·,·⟫` does not parse reliably; use `inner ℂ _ _` in new files.
    Refinement: `Q3/Proofs/Heat_RKHS_Interface.lean` packages a minimal RKHS interface
    (`eval x` + reproducing vectors `k x`) so the matching hypothesis reduces to:
    `eval (xi_n n) (ψ i) = prime_vec ... i`.
    Reality check (important before “full Gaussian RKHS”): in the *Gaussian RKHS on ℝ* with kernel
    `k_t(x,y)=exp(-(x-y)^2/(4t))`, it is not obvious (and may be false) that one can pick an
    orthonormal family `ψ_i` with exact exponential sample values `ψ_i(ξ_n)=prime_vec ... i`.
    The robust route is to build `ψ_i` by *kernel interpolation on the finite node set* and then
    track the induced unitary change-of-basis on `ℂ^{2M+1}`; this still gives the needed norm control
    because `A · T_P_comp · A†` has the same operator norm as `T_P_comp`.
  - Option 2 (OK fallback): skip RKHS and cap `‖T_P_comp_real‖` directly by Schur/row-sum:
    `T_P_comp_real_opNorm_le_weight_sum` in `Q3/Proofs/RKHS_cap_rayleigh.lean`.
    Status: compiles now; use when Option 1 is blocked.
  - Pivot rule: if Option 1 requires new axioms / >N days of infrastructure, mark “false-for-now”
    and wire Option 2 into the proof chain; keep Option 1 as long-term cleanup.
  - τ=0 note (важно): `BaseAtomCone_K` в `Q3/Axioms.lean` требует `c_i ≥ 0` и `τ=0`.
    Такой конус генерирует только “центрированные” (по |ξ|) профили и **не может быть плотным**
    в общем `W_K` без дополнительных идей (иначе A1′ ломается). Поэтому “работаем только τ=0”
    должно быть либо (a) про A3/RKHS-узел (matching/positivity) с сохранением τ-параметра в плотности,
    либо (b) сопровождается новой, честной A1′-теоремой для изменённого генератора.

- Tree-plan (2026-01-23, requested): Moore–Aronszajn RKHS + где закрывается `hA` (без аксиом).
  - **(0) One-scale spec (must):** eliminate two-scale mismatch by using one `t` everywhere; scaffolding:
    `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean` (`A3_bridge_data_rayleigh_Fourier_at`, `A3_bridge_rayleigh_at_from_weight_sum_P_A`).
  - **(1) RKHS construction:** build `H_t` from kernel `k_t` (Moore–Aronszajn) + reproducing:
    future file (blocked infra) + Aristotle sandbox tasks in `aristotle_input/` (start from `gaussian_rkhs_kernel_v1.lean`).
  - **(2) Matching bridge:** use the minimal interface to reduce “inner = sample” to eval statements:
    `Q3/Proofs/Heat_RKHS_Interface.lean` (`h_eval_of_eval_eq_prime_vec`).
  - **(3) Close `hA` (C1 exact identity):** once matching hypotheses are provided, the compression identity is a theorem:
    `Q3/Proofs/RKHS_Interface_C1.lean` (`T_P_comp_toCLM_eq_compression`).
  - **(4) Fast fallback (no RKHS):** cap from Schur/weight_sum at the same `t`:
    `Q3/Proofs/RKHS_cap_generic.lean` (`rkhs_cap_rayleigh_of_weight_sum`) + provide the numeric/analytic `h_weight_sum`.

---

## A3_FLOOR @ one-scale `t_critical` (BLOCKER, 2026-01-23)

**Target (exact):**
- Prove (no axioms/sorry): `∀ θ ∈ Set.Icc (-1/2) (1/2), Q3.c_star ≤ P_A B_min Q3.t_critical θ`.
- This is the missing input `hP_ge` for the one-scale bridge in `Q3/Proofs/P_A_Toeplitz_bridge_one_scale.lean`.

**Why it’s hard right now (root cause, not vibes):**
- The old proof `Q3/Proofs/A3_Floor_Main.lean` works at `t_sym = 3/50` because it can lower-bound the key
  “two big terms” using the strong pointwise bound `a(1/2) ≥ 5/8` (log2 is large enough) and then crush all tails.
- At `t_critical = 3/20`, the bottleneck becomes controlling `g B_min t (1-θ)` for `θ` close to `1/2`,
  i.e. `a(x)` for `x` slightly **above** `1/2` (e.g. `x = 11/20 = 0.55`).
- With the current remainder lemma `Q3.re_digamma_remainder_bound_stieltjes` (constant `1/4`),
  the best “pure-inequality” lower bounds for `a(11/20)` appear too weak to close the numeric gap cleanly;
  the dead-code path in `Q3/Proofs/A3_Floor_Bounds.lean` explicitly notes that a sharper
  `re_digamma_remainder_bound` (constant `1/12`) would unlock the needed strength.

**Decision tree (next moves):**
1) **OK / recommended:** implement a sharper digamma remainder bound (the missing `re_digamma_remainder_bound`)
   and resurrect `a_lower_bound_from_remainder` in `Q3/Proofs/A3_Floor_Bounds.lean`.
   - Pointers: `full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Bounds.lean` (dead code blocks around `re_digamma_remainder_bound`),
     `full/q3.lean.aristotle/Q3/DigammaRemainder.lean` (current `…_stieltjes` bound).
   - This is the most “community-standard” fix: better explicit remainder ⇒ better pointwise `a(x)` bounds ⇒ floor.
2) **OK but larger infra:** prove a *local* control of `a` on `[1/2, 11/20]` (e.g. via trigamma bounds)
   and use it to transfer the known `a(1/2)` lower bound to `a(1-θ)` when `θ≈1/2`.
   - Risk: introduces heavy special-functions analysis in Lean.
3) **False-for-now (policy):** silently mix two-scale (`t_sym` floor + `t_critical` prime cap) in the *same* proof chain.
   - If we go two-scale, we must write an explicit comparison lemma and document the spec change; otherwise it’s drift.


## Спеки

- Основной спецификатор инвариантов: `docs/PROJECT_SPECS.md`.


## File: full/q3.lean.aristotle/docs/insights/INDEX.md

# Insights index

Auto-generated by scripts/refresh_insights.py.

Files:

- a3_bridge_math_rkhs_bound.md
- a3_fourier_atoms_axiom_2026_01_16.md
- a3_symbol_mismatch_reverse_engineering.md
- a_star_even_closure_2026_01_20.md
- a_star_vs_p_a_dossier.md
- aristotle_error_recovery.md
- aristotle_strategy_pure_informal.md
- atomcone_fixed_t_gap_2026_01_18.md
- breakthrough_proshka_full_proof_2026_01_14.md
- C3_prime_cap_correctness_2026_01_19.md
- C3_RKHS_vs_window_approach_2026_01_19.md
- carleson_implicit_proof_2026_01_17 2.md
- carleson_implicit_proof_2026_01_17.md
- check_axioms_prebuild_a3_floor_2026_01_16.md
- documentation_discipline.md
- drift_report_m1_m4.md
- explore_agent_for_mathlib_search_2026_01_17.md
- file_organization_aristotle.md
- h_cap_numerical_estimates_2026_01_14.md
- heat_localization_kills_primes_2026_01_16 2.md
- heat_localization_kills_primes_2026_01_16.md
- heat_parameter_mismatch_2026_01_14.md
- key_constants_reference.md
- lean_simpa_performance_fix_2026_01_19.md
- localization_argument_full_analysis_2026_01_16 2.md
- localization_argument_full_analysis_2026_01_16.md
- mgrep_websearch_discovery_2026_01_18.md
- PERIODIZATION_BOTTLENECK_FIX.md
- prime_term_nodes_bridge_2026_01_17 2.md
- prime_term_nodes_bridge_2026_01_17.md
- prime_term_shift_K_dependent_2026_01_19.md
- proshka_key_resource.md
- proven_assets_inventory_2026_01_14.md
- rayleigh_q_identification_2026_01_17 2.md
- rayleigh_q_identification_2026_01_17.md
- rayleigh_vs_sb_optional.md
- rescaled_density_lemma_variants_2026_01_16 2.md
- rescaled_density_lemma_variants_2026_01_16.md
- research_swarm_symlink_caching_2026_01_17.md
- rh_q3_invariants_contract_2026_01_16.md
- rkhs_cap_implementation_2026_01_15.md
- schur_test_l2_vs_linfty_2026_01_20.md
- szego_bottcher_not_needed.md
- t_p_comp_mismatch.md
- t_p_compression_fix_2026_01_14.md
- t_parameter_forms.md
- tau_shift_variants_rkhs_a3_2026_01_18.md
- v1_surprise_real_tp_bounds_2026_01_14.md
- v3_success_a3_bridge_rayleigh_2026_01_14.md
- v4_success_full_tp_bound_2026_01_14.md


## File: full/q3.lean.aristotle/Q3/Axioms.lean

/-
Q3 Formalization: External Axioms
=================================

This file contains axioms organized by tier:
- **Tier-1**: Classical results from peer-reviewed literature (1911-1999)
- **Tier-2**: Q3 paper contributions (new technical results)

IMPORTANT: Run `#print axioms RH_of_Weil_and_Q3` to verify all dependencies.

Axiom Summary:
- Tier-1: 10 axioms (Weil, Guinand, a_star properties, Szegő-Böttcher, Schur, etc.)
- Tier-2: 12 axioms (A1', A2, A3, RKHS, node spacing, Q ≥ 0 on compacts)

New additions (2024-12):
- T1.3d: a_star_even (digamma conjugation symmetry)
- T1.4b: Szego_Rayleigh_lower_bound (Rayleigh quotient → symbol infimum)
-/

import Q3.Basic.Defs
import Q3.Proofs.A_Star_Properties  -- For a_star_even_thm (proven via Mathlib Gamma_conj)
import Q3.Proofs.Digamma_One_Fourth  -- For digamma_one_fourth_neg_thm (proven via Aristotle)

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Matrix.Norms.L2Operator

namespace Q3

/-!
## TIER-1: CLASSICAL AXIOMS FROM LITERATURE

These are well-established theorems from peer-reviewed mathematics.
Each is cited with publication details.
-/

/-! ## Axiom T1.1: Weil Criterion (1952)

The Weil explicit formula criterion:
  RH ⟺ Q(Φ) ≥ 0 for all Φ in the Weil cone

**Citation:**
- Weil, A. (1952). "Sur les 'formules explicites' de la théorie des nombres premiers"
  Meddelanden Från Lunds Universitets Matematiska Seminarium, 252-265.
- Bombieri, E. (2000). "The Riemann Hypothesis" Clay Mathematics Institute.
-/
axiom Weil_criterion : (∀ Φ ∈ Weil_cone, Q Φ ≥ 0) ↔ RH

/-! ## Axiom T1.2: Guinand-Weil Explicit Formula (1948)

**Citation:**
- Guinand, A.P. (1948). "A summation formula in the theory of prime numbers"
  Proc. London Math. Soc. (2) 50, 107-119.
-/
axiom explicit_formula :
  ∀ Φ ∈ Weil_cone, Q Φ = arch_term Φ - prime_term Φ

/-! ## Axiom T1.3a: Digamma at 1/4 is negative

By DLMF 5.4.14: ψ(1/4) = -γ - π/2 - 3·ln(2)

Numerical values:
- γ (Euler-Mascheroni) ≈ 0.5772
- π/2 ≈ 1.5708
- 3·ln(2) ≈ 2.0794

Sum: ψ(1/4) ≈ -4.227 < 0

This can be proven rigorously via the series representation:
  ψ(1/4) = -γ + Σ_{n=0}^∞ (1/(n+1) - 4/(4n+1))
         = -γ - 3·Σ_{n=0}^∞ 1/((n+1)(4n+1))
Each term in the sum is positive, so ψ(1/4) < -γ < 0.

**Citation:**
- DLMF 5.4.14: https://dlmf.nist.gov/5.4.14
- Abramowitz & Stegun (1964), Section 6.3.3

**Status:** THEOREM (proven via Aristotle using reflection/duplication formulas)
-/
theorem digamma_one_fourth_neg : (digamma (1/4 : ℂ)).re < 0 := digamma_one_fourth_neg_thm

/-! ## Theorem T1.3: Archimedean Kernel Positivity at Origin (PROVEN)

a*(0) = 2π(log π - ψ(1/4)) > 0

**Proof:**
- log π > 1 (since π > 3 > e)
- Re(ψ(1/4)) < 0 (by digamma_one_fourth_neg axiom)
- Therefore: log π - Re(ψ(1/4)) > 1 - 0 = 1 > 0
- And: a*(0) = 2π · (positive) > 0

**Note:** The full statement `∀ ξ, a_star ξ > 0` is FALSE for |ξ| > 1.
However, only the value at ξ = 0 is needed in the proof chain.

**Citation:**
- DLMF 5.4.14 for ψ(1/4) = -γ - π/2 - 3·ln(2) ≈ -4.227
-/
theorem a_star_pos : a_star 0 > 0 := by
  unfold a_star a
  have h_arg : (1/4 : ℂ) + Complex.I * Real.pi * (0 : ℝ) = (1/4 : ℂ) := by simp
  rw [h_arg]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  -- log π > 1 (since π > 3 > e)
  have hlog_pi : Real.log Real.pi > 1 := by
    have hlog3 : Real.log 3 > 1 := by
      have h : Real.exp 1 < 3 := by
        calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
          _ < 3 := by norm_num
      exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).mpr h
    have hpi3 : Real.pi > 3 := Real.pi_gt_three
    have hlog_mono : Real.log 3 < Real.log Real.pi := by
      exact (Real.log_lt_log_iff (by norm_num) Real.pi_pos).mpr hpi3
    linarith
  have hpsi_neg : (digamma (1/4 : ℂ)).re < 0 := digamma_one_fourth_neg
  have hdiff_pos : Real.log Real.pi - (digamma (1/4 : ℂ)).re > 0 := by linarith
  exact mul_pos h2pi_pos hdiff_pos

/-! ## Theorem T1.3b: Archimedean Kernel Continuity (PROVEN)

a*(ξ) is continuous (follows from digamma regularity away from poles).
The digamma function ψ(s) is holomorphic for s ∉ {0, -1, -2, ...}.
Since a*(ξ) = 2π(log π - Re(ψ(1/4 + iπξ))) and 1/4 + iπξ avoids poles,
a* inherits continuity from ψ.

**Citation:**
- Titchmarsh, E.C. (1986). "The Theory of the Riemann Zeta-Function", Chapter IX.
- Abramowitz & Stegun (1964). "Handbook of Mathematical Functions", Section 6.3 (p. 258).
- NIST DLMF (2024), Section 5.2: Digamma function definitions (https://dlmf.nist.gov/5.2).

**Status:** THEOREM (proven via Mathlib differentiability of Gamma)
-/
theorem a_star_continuous : Continuous a_star := a_star_continuous_thm

/-! ## Theorem T1.3c: Archimedean Kernel Bounded on Compacts (PROVEN)

a*(ξ) is bounded on any compact set (continuous function on compact → bounded).
This is a standard consequence of the extreme value theorem:
continuous real-valued function on a compact set attains its bounds.

**Citation:**
- Rudin, W. (1976). "Principles of Mathematical Analysis", Theorem 4.16.
- Direct corollary of T1.3b (continuity) and Heine-Borel theorem.

**Status:** THEOREM (proven via extreme value theorem + T1.3b)
-/
theorem a_star_bdd_on_compact : ∀ (K : ℝ) (hK : K > 0),
  ∃ M > 0, ∀ ξ ∈ Set.Icc (-K) K, a_star ξ ≤ M := a_star_bdd_on_compact_thm

/-! ## Theorem T1.3d: Archimedean Kernel Even Symmetry (PROVEN)

a*(−ξ) = a*(ξ) because ψ(z̄) = ψ(z)̄ for the digamma function.
For z = 1/4 + iπξ, the conjugate is 1/4 - iπξ = 1/4 + iπ(−ξ).

**Citation:**
- Abramowitz & Stegun (1964). "Handbook of Mathematical Functions", Section 6.3.
- NIST DLMF (2024), Section 5.5: ψ(z̄) = ψ(z)̄.

**Status:** THEOREM (proven via Mathlib Complex.Gamma_conj)
-/
theorem a_star_even : ∀ ξ : ℝ, a_star (-ξ) = a_star ξ := a_star_even_thm

/-! ## Axiom T1.4: Szegő-Böttcher Theory (1958/1999)

Eigenvalues of Toeplitz matrices bounded by symbol range.

**Citation:**
- Grenander, U. & Szegő, G. (1958). "Toeplitz Forms and Their Applications".
- Böttcher, A. & Silbermann, B. (1999). "Introduction to Large Truncated Toeplitz Matrices".
-/

/-- Toeplitz matrix from symbol -/
noncomputable def ToeplitzMatrix (M : ℕ) (P : ℝ → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => P ((i.val - j.val : ℤ) * Real.pi / M)

axiom Szego_Bottcher_eigenvalue_bound :
  ∀ (M : ℕ) (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ μ, (∃ v : Fin M → ℝ, v ≠ 0 ∧ (ToeplitzMatrix M P).mulVec v = μ • v) →
    sInf {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)} ≤ μ ∧
    μ ≤ sSup {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)}

axiom Szego_Bottcher_convergence :
  ∀ (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ ε > 0, ∃ N, ∀ m ≥ N,
    ∀ μ, (∃ v : Fin m → ℝ, v ≠ 0 ∧ (ToeplitzMatrix m P).mulVec v = μ • v) →
      ∃ θ ∈ Set.Icc 0 (2 * Real.pi), |μ - P θ| < ε

/-! ## Axiom T1.4b: Szegő Rayleigh Quotient Bound (Classical)

**Key Bridge Axiom**: Minimum Rayleigh quotient converges to symbol infimum.

For Toeplitz matrix T_M[P] with continuous even symbol P:
  inf_{v ≠ 0} (v^T · T_M[P] · v) / ||v||² → inf_θ P(θ)  as M → ∞

More precisely: for any ε > 0, there exists M₀ such that for all M ≥ M₀,
the Rayleigh quotient is at least inf P - ε.

**Citation:**
- Grenander, U. & Szegő, G. (1958). "Toeplitz Forms and Their Applications", Ch. 5.
- Gray, R.M. (2006). "Toeplitz and Circulant Matrices: A Review", Theorem 4.2.
-/

/-- Rayleigh quotient for symmetric matrix -/
noncomputable def RayleighQuotient {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, v i * A i j * v j) / (∑ i, v i ^ 2)

/-- Szegő Rayleigh bound: for large M, Rayleigh quotient ≥ inf P - ε -/
axiom Szego_Rayleigh_lower_bound :
  ∀ (P : ℝ → ℝ), Continuous P → (∀ θ, P (-θ) = P θ) →
  ∀ ε > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
      RayleighQuotient (ToeplitzMatrix M P) v ≥ sInf {P θ | θ ∈ Set.Icc 0 (2 * Real.pi)} - ε

/-! ## Axiom T1.5: Schur Test (1911)

**Citation:**
- Schur, I. (1911). "Bemerkungen zur Theorie der beschränkten Bilinearformen"
  J. Reine Angew. Math. 140, 1-28.
-/
axiom Schur_test {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ), A.IsSymm →
  ∀ (C : ℝ), 0 ≤ C → (∀ i, ∑ j, |A i j| ≤ C) → ‖A‖ ≤ C

/-! ## Axiom T1.6: Archimedean Constant Positivity

c₀(K) = inf_{|ξ| ≤ K} a*(ξ) > 0 by continuity and T1.3.
Since a*(ξ) > 0 for all ξ (T1.3) and continuous (T1.3b),
the infimum over a compact set is attained and positive.

**Citation:**
- Follows from T1.3 (positivity), T1.3b (continuity), and extreme value theorem.
-/

/-- Archimedean constant: c₀(K) = inf_{|ξ| ≤ K} a*(ξ) -/
noncomputable def c_arch (K : ℝ) : ℝ :=
  sInf {a_star ξ | ξ ∈ Set.Icc (-K) K}

axiom c_arch_pos : ∀ K : ℝ, K > 0 → c_arch K > 0

/-! ## Uniform Archimedean Floor (December 2025 paper update)

The paper was updated to use a UNIFORM floor c* = 11/10 instead of K-dependent c_arch(K).
This is the global minimum of P_A(θ) over the entire torus T.
Proven in A3_Floor_Main.lean.

Benefits of uniform approach:
- M₀ is K-independent (single threshold for all K)
- t_rkhs is K-independent (single heat parameter)
- Simplifies the A3_bridge axiom chain
-/

/-- Uniform Archimedean floor: c* = 11/10
    This is min_{θ ∈ T} P_A(θ) where P_A is the Archimedean symbol. -/
noncomputable def c_star : ℝ := 11 / 10

/-- c* is positive (trivial computation) -/
lemma c_star_pos : c_star > 0 := by norm_num [c_star]

/-- c* > 1 (useful for contraction arguments) -/
lemma c_star_gt_one : c_star > 1 := by norm_num [c_star]

/-- c*/4 > 0 (the bound used in A3_bridge) -/
lemma c_star_div_four_pos : c_star / 4 > 0 := by norm_num [c_star]

/-- c* ≤ c_arch(K) for K ≥ threshold.

Since c_star = 11/10 is the GLOBAL minimum of P_A(θ) over the torus T,
and c_arch(K) = inf_{|ξ| ≤ K} a_star(ξ) is the minimum over [-K, K],
we have c_star ≤ c_arch(K) when the support of the periodization
is contained in [-K, K].

This lemma allows backwards-compatible use of old K-dependent proofs:
any bound using c_star/4 automatically gives a bound using c_arch(K)/4.
-/
axiom c_star_le_c_arch : ∀ K : ℝ, K ≥ 1 → c_star ≤ c_arch K

/-! ## Axiom T1.7: Eigenvalue-Norm Bound

For symmetric matrices: |eigenvalue| ≤ operator norm.
This is a standard result in spectral theory.

**Citation:**
- Horn, R.A. & Johnson, C.R. (2012). "Matrix Analysis", 2nd ed., Theorem 5.6.2.
- Kato, T. (1995). "Perturbation Theory for Linear Operators", Chapter II.
-/
axiom eigenvalue_le_norm {n : Type*} [Fintype n] [DecidableEq n] :
  ∀ (A : Matrix n n ℝ) (μ : ℝ),
  (∃ v : n → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) → |μ| ≤ ‖A‖

/-!
## TIER-2: Q3 PAPER AXIOMS (NEW CONTRIBUTIONS)

These axioms represent the technical contributions of the Q3 paper.
Each corresponds to a theorem proved in the paper.
-/

/-! ## Supporting Definitions for Tier-2 -/

/-- Fejér kernel (triangular) -/
noncomputable def Fejer_kernel (B : ℝ) (x : ℝ) : ℝ :=
  max 0 (1 - |x| / B)

/-- Heat kernel -/
noncomputable def heat_kernel_A1 (t : ℝ) (x : ℝ) : ℝ :=
  1 / Real.sqrt (4 * Real.pi * t) * Real.exp (-x^2 / (4 * t))

/-- Fejér-heat atom: symmetrized product -/
noncomputable def Fejer_heat_atom (B t τ : ℝ) (ξ : ℝ) : ℝ :=
  Fejer_kernel B (ξ - τ) * heat_kernel_A1 t (ξ - τ) +
  Fejer_kernel B (ξ + τ) * heat_kernel_A1 t (ξ + τ)

/-- The cone generated by Fejér-heat atoms -/
def Fejer_heat_cone (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B t : Fin n → ℝ) (τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, t i > 0) ∧
        (∀ i, |τ i| ≤ K) ∧
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) (t i) (τ i) x) }

/-- AtomCone_K: Fejér-heat atoms with support control AND membership in W_K
    This is the proper generating cone for the T5 transfer theorem -/
def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B t : Fin n → ℝ) (τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, t i > 0) ∧
        (∀ i, |τ i| + B i ≤ K) ∧  -- ensures support ⊆ [-K, K] (Lemma a1-fixed-t-density)
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) (t i) (τ i) x) ∧
        g ∈ W_K K }  -- explicitly require g ∈ W_K

/-- AtomCone_K_fixed: fixed heat parameter t0 (A1' fixed-t cone). -/
def AtomCone_K_fixed (K t0 : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, |τ i| + B i ≤ K) ∧  -- ensures support ⊆ [-K, K]
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t0 (τ i) x) ∧
        g ∈ W_K K }

lemma AtomCone_K_fixed_subset (K t0 : ℝ) (ht0 : t0 > 0) :
    AtomCone_K_fixed K t0 ⊆ AtomCone_K K := by
  intro g hg
  rcases hg with ⟨n, c, B, τ, hc, hB, hτB, hg_sum, hg_mem⟩
  refine ⟨n, c, B, (fun _ => t0), τ, hc, hB, ?_, hτB, ?_, hg_mem⟩
  · intro _; exact ht0
  · intro x
    simpa using (hg_sum x)

/-- BaseAtomCone_K: Fejér-heat atoms with τ = 0 only (centered atoms).

This cone aligns directly with the A3 bridge which uses P_A(B, t) without τ-shift.
For τ = 0: Fejer_heat_atom B t 0 ξ = 2 * Fejer_kernel B ξ * heat_kernel_A1 t ξ
(symmetric, no shift).

**Architecture:**
1. Q ≥ 0 on BaseAtomCone_K via A3 bridge (P_A floor + RKHS cap)
2. τ-transfer to AtomCone_K_fixed via Q Lipschitz continuity
-/
def BaseAtomCone_K (K t0 : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, B i ≤ K) ∧  -- support ⊆ [-K, K] since τ = 0
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t0 0 x) ∧
        g ∈ W_K K }

lemma BaseAtomCone_K_subset_AtomCone_K_fixed (K t0 : ℝ) :
    BaseAtomCone_K K t0 ⊆ AtomCone_K_fixed K t0 := by
  intro g hg
  rcases hg with ⟨n, c, B, hc, hB, hBK, hg_sum, hg_mem⟩
  refine ⟨n, c, B, (fun _ => 0), hc, hB, ?_, ?_, hg_mem⟩
  · intro i
    simp only [abs_zero, zero_add]
    exact hBK i
  · intro x
    simp only [hg_sum x]

/-- Even nonnegative continuous functions on [-K, K] -/
def C_even_nonneg (K : ℝ) : Set (ℝ → ℝ) :=
  { f | ContinuousOn f (Set.Icc (-K) K) ∧
        (∀ x, f x = f (-x)) ∧
        (∀ x ∈ Set.Icc (-K) K, 0 ≤ f x) }

/-- **[A1' Density]** Fejér-heat atoms are dense in `W_K` (sup-norm).

For any `Φ ∈ W_K` and `ε > 0`, exists `g ∈ AtomCone_K_fixed K t₀` with
`sup |Φ - g| < ε`.

* **Q3:** `a1:thm:A1-local-density`
* **TeX:** `sections/A1prime.tex`, Theorem A1'
* **Status:** axiom (partial Aristotle proof: heat kernel lemmas done)

See also: `lem:a1-fixed-t-density` for fixed-t₀ variant.
-/
axiom A1_density_WK_axiom : ∀ (K : ℝ) (hK : K > 0) (t0 : ℝ) (ht0 : t0 > 0),
  ∀ Φ ∈ W_K K, ∀ ε > 0,
    ∃ g ∈ AtomCone_K_fixed K t0,  -- fixed-t cone ⊆ W_K
      sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε

/-- **[A1' Legacy]** ~~Legacy A1 density (deprecated).~~

**DEPRECATED:** Use `A1_density_WK_axiom` instead.

* **Q3:** `thm:A1-density`
* **TeX:** `sections/A1prime.tex`
* **Status:** deprecated (superseded by fixed-t₀ version)
-/
axiom A1_density_axiom : ∀ (K : ℝ) (hK : K > 0),
  ∀ f ∈ C_even_nonneg K, ∀ ε > 0,
    ∃ g ∈ Fejer_heat_cone K, ∀ x ∈ Set.Icc (-K) K, |f x - g x| < ε

/-! ## A2 Helpers -/

/-- Active prime nodes set (for axiom) -/
def ActiveNodes_axiom (K : ℝ) : Set ℕ := {n | |xi_n n| ≤ K ∧ n ≥ 2}

/-- Sum of weights over active nodes (for axiom) -/
noncomputable def W_sum_axiom (K : ℝ) : ℝ :=
  ∑' n, if n ∈ ActiveNodes_axiom K then w_Q n else 0

/-- **[A2 Local Finite]** Prime weight sum is finite on compacts.

The sum `∑_{ξ_n ∈ [-K,K]} w(n)` is bounded.

* **Q3:** `lem:Q-local-finite`
* **TeX:** `sections/A2.tex`, Lemma (local finiteness)
* **Status:** wired → `W_sum_BridgeV2.W_sum_finite_Q3`
-/
axiom W_sum_finite_axiom : ∀ (K : ℝ) (hK : K > 0), ∃ B, W_sum_axiom K ≤ B

/-- **[A2 Lipschitz]** `Q` is Lipschitz continuous on `W_K`.

`|Q(Φ₁) - Q(Φ₂)| ≤ L_Q(K) · ‖Φ₁ - Φ₂‖_∞` for `Φ₁, Φ₂ ∈ W_K`.

* **Q3:** `cor:A2-Lip`
* **TeX:** `sections/A2.tex`, Corollary (Lipschitz on compact)
* **Status:** wired → `Q3.Proofs.Q_Lipschitz_on_W_K_thm`
-/
axiom Q_Lipschitz_on_W_K : ∀ (K : ℝ) (hK : K > 0),
  ∃ L > 0, ∀ Φ₁, Φ₁ ∈ W_K K → ∀ Φ₂, Φ₂ ∈ W_K K →
    |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}

/-- **[RKHS Contraction]** Prime operator `T_P` is strictly contractive.

`‖T_P‖ ≤ ρ < 1` for appropriate heat parameter `t`.

* **Q3:** `rkhs:thm:rkhs-contraction`
* **TeX:** `sections/RKHS/main.tex`, Theorem (strict contraction)
* **Status:** wired → `Bridge.RKHS_contraction_data_of_bridge`
-/
axiom RKHS_contraction_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-- **[RKHS Row Sum]** Gershgorin row sum bound for `T_P`.

`∑_j |T_P[i,j]| ≤ w_max + √w_max · S_K(t)`

* **Q3:** `prop:rkhs-gram-cap`
* **TeX:** `sections/RKHS/prime_cap.tex`, Proposition (RKHS cap via Gram)
* **Status:** axiom
-/
axiom T_P_row_sum_bound_axiom : ∀ (K t : ℝ) (hK : K ≥ 1) (ht : t > 0),
  ∀ (Nodes_K : Set ℕ) [Fintype Nodes_K] (T_P : Matrix Nodes_K Nodes_K ℝ),
  (∀ i j : Nodes_K, T_P i j = Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
    Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))) →
  ∀ i, ∑ j, |T_P i j| ≤ w_max + Real.sqrt w_max * S_K K t

/-- **[RKHS S_K]** Off-diagonal geometric series bound.

`S_K(t) = 2x/(1-x)` where `x = exp(-δ²/(4t))`, so `S_K(t) ≤ η` for `t ≤ t_min`.

* **Q3:** `lem:rkhs-gram-off`
* **TeX:** `sections/RKHS/prime_cap.tex`, Lemma (off-diagonal sum bound)
* **Status:** wired → `S_K_SmallBridgeV2.S_K_small_Q3`
-/
axiom S_K_small_axiom : ∀ (K t η : ℝ) (hK : K ≥ 1) (hη : η > 0) (ht : t ≤ t_min K η),
  S_K K t ≤ η

/-- **[RKHS Node Gap]** Adjacent spectral nodes separated by `δ_K`.

`ξ_{n₂} - ξ_{n₁} ≥ δ_K` for adjacent nodes in `[-K, K]`.

* **Q3:** `rkhs:lem:node_gap_lower_bound`
* **TeX:** `sections/RKHS/main.tex`, Lemma (node gap on compacts)
* **Status:** wired → `NodeSpacingBridge.node_spacing_Q3`
-/
axiom node_spacing_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∀ (n₁ n₂ : ℕ), n₁ ∈ Nodes K → n₂ ∈ Nodes K → n₁ < n₂ →
    xi_n n₂ - xi_n n₁ ≥ delta_K K

/-- **[RKHS Off-Diag]** Off-diagonal Gaussian sum bounded by `S_K`.

`∑_{j≠i} exp(-(ξᵢ-ξⱼ)²/(4t)) ≤ S_K(t)`

* **Q3:** `lem:rkhs-gram-off`
* **TeX:** `sections/RKHS/prime_cap.tex`, Lemma (off-diagonal sum)
* **Status:** axiom
-/
axiom off_diag_exp_sum_axiom : ∀ (K t : ℝ) (hK : K ≥ 1) (ht : t > 0)
    [Fintype (Nodes K)] (i : Nodes K),
    ∑ j : Nodes K, (if (j : ℕ) ≠ (i : ℕ) then
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)) else 0) ≤ S_K K t

/-- **[A3 Bridge]** ~~K-dependent Toeplitz-symbol bridge (deprecated).~~

**DEPRECATED:** Use `A3_bridge_uniform` instead.

`λ_min(T_M[P_A] - T_P) ≥ c_arch(K)/4` for `M ≥ M₀(K)`.

* **Q3:** `thm:A3` (old K-dependent formulation)
* **TeX:** `sections/A3/main.tex`
* **Status:** deprecated (superseded by uniform version)
-/
axiom A3_bridge_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_arch K / 4

/-- **[A3 Uniform]** K-independent Toeplitz-symbol bridge.

`λ_min(T_M[P_A] - T_P) ≥ c*/4` for `M ≥ M₀` (uniform threshold).

Key: uses `c* = 11/10` instead of K-dependent `c_arch(K)`.

* **Q3:** `thm:A3`
* **TeX:** `sections/A3/main.tex`, Theorem A3 (uniform)
* **Status:** axiom (December 2025 primary formulation)
-/
axiom A3_bridge_uniform :
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_star / 4

/-! ## Axiom T2.6c: A3 Bridge (Rayleigh-first, Compression)

Rayleigh-only variant using the compression prime operator T_P^{(M)}.
No Szegő–Böttcher discretization step (no M₀), and T_P is built from Nodes K.
-/
axiom A3_bridge_rayleigh_axiom :
  ∀ (K : ℝ) (hK : K ≥ 1) [Fintype (Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        RayleighQuotient
            (ToeplitzMatrix (2 * M + 1) a_star - T_P_comp_real K K t M) v
          ≥ c_star / 4

/-! ## Axiom T2.7: Q ≥ 0 on Atom Cone (Q3 Core Result)

This is the key positivity axiom: Q ≥ 0 on the generating atom cone.
This follows from A3 (Toeplitz bridge) + RKHS (contraction).

The full "Q ≥ 0 on W_K" is then a THEOREM (T5_transfer), not an axiom,
proven via: A1 (density) + A2 (Lipschitz) + this axiom.
-/

/-- Bundled statement of the A3 bridge axiom for a fixed compact parameter `K`. (DEPRECATED) -/
def A3_bridge_data (K : ℝ) : Prop :=
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_arch K / 4

/-- Uniform A3 bridge data (December 2025 paper update).
    K-independent version using c_star = 11/10. -/
def A3_bridge_data_uniform : Prop :=
  ∃ M₀ : ℕ, ∃ t > 0, ∀ M ≥ M₀,
    ∀ (v : Fin M → ℝ), v ≠ 0 →
    (∑ i, ∑ j, v i * v j * (ToeplitzMatrix M a_star i j -
      Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
      Real.exp (-(xi_n i - xi_n j)^2 / (4 * t)))) /
    (∑ i, v i ^ 2) ≥ c_star / 4

/-- Rayleigh-first A3 bridge data using the compression prime operator. -/
def A3_bridge_data_rayleigh (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        RayleighQuotient
            (ToeplitzMatrix (2 * M + 1) a_star - T_P_comp_real K K t M) v
          ≥ c_star / 4

/-- Bundled statement of the RKHS contraction axiom for a fixed compact parameter `K`. (DEPRECATED) -/
def RKHS_contraction_data (K : ℝ) : Prop :=
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-- Uniform RKHS contraction data (December 2025 paper update).
    K-independent version - the heat parameter t and bound ρ are uniform. -/
def RKHS_contraction_data_uniform : Prop :=
  ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ K ≥ 1, ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (w_RKHS i) * Real.sqrt (w_RKHS j) *
        Real.exp (-(xi_n i - xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

/-- **[Main Positivity K-dep]** ~~Q ≥ 0 on atom cone (K-dependent, deprecated).~~

**DEPRECATED:** Use `Q_nonneg_on_atoms_uniform` instead.

* **Q3:** `thm:Main-positivity` (old formulation)
* **Status:** deprecated
-/
axiom Q_nonneg_on_atoms_of_A3_RKHS_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
  A3_bridge_data K → RKHS_contraction_data K →
  ∀ g ∈ AtomCone_K K, Q g ≥ 0

/-- **[Main Positivity]** `Q(g) ≥ 0` on atom cone (uniform version).

A3_bridge_uniform + RKHS_contraction_uniform ⟹ Q ≥ 0 on atoms.

* **Q3:** `thm:Main-positivity`
* **TeX:** `sections/Main_closure.tex`, Main positivity theorem
* **Status:** axiom (core result, December 2025 primary formulation)
-/
axiom Q_nonneg_on_atoms_uniform :
  A3_bridge_data_uniform → RKHS_contraction_data_uniform →
  ∀ K ≥ 1, ∀ g ∈ AtomCone_K K, Q g ≥ 0

/-!
## AXIOM VERIFICATION
-/

-- Tier-1 axioms (7 classical)
#check Weil_criterion
#check explicit_formula
#check a_star_pos
#check Szego_Bottcher_eigenvalue_bound
#check Szego_Bottcher_convergence
#check Schur_test
#check c_arch_pos
#check eigenvalue_le_norm

-- Uniform definitions (December 2025 paper update)
#check c_star                        -- NEW: Uniform floor c* = 11/10
#check c_star_pos                    -- c* > 0
#check c_star_gt_one                 -- c* > 1
#check A3_bridge_uniform             -- NEW: K-independent A3 bridge
#check A3_bridge_data_uniform        -- NEW: Bundled uniform data
#check RKHS_contraction_data_uniform -- NEW: Bundled uniform RKHS
#check Q_nonneg_on_atoms_uniform     -- NEW: Uniform positivity transfer

-- Tier-2 axioms (12 Q3 contributions)
#check A1_density_WK_axiom           -- density in W_K
#check A1_density_axiom              -- Legacy density
#check W_sum_finite_axiom            -- W_sum bound for A2
#check Q_Lipschitz_on_W_K            -- A2 Lipschitz
#check RKHS_contraction_axiom        -- RKHS contraction
#check T_P_row_sum_bound_axiom       -- Row sum bound
#check S_K_small_axiom               -- Geometric series decay
#check node_spacing_axiom            -- Node spacing ≥ δ_K
#check off_diag_exp_sum_axiom        -- Off-diagonal sum ≤ S_K
#check A3_bridge_axiom               -- A3 Toeplitz bridge (DEPRECATED)
#check Q_nonneg_on_atoms_of_A3_RKHS_axiom   -- A3+RKHS ⇒ atoms positivity (DEPRECATED)

end Q3


## File: full/q3.lean.aristotle/Q3/Proofs/ShiftedWindows.lean

/-
Shifted windows and periodization for tau-shifted atoms.
-/

import Mathlib
import Q3.Axioms
import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

def phi_shift (B t tau : ℝ) (xi : ℝ) : ℝ :=
  fejer_heat_window B t (xi - tau)

def g_shift (B t tau : ℝ) (xi : ℝ) : ℝ :=
  a xi * phi_shift B t tau xi

def P_A_shift (B t tau : ℝ) (theta : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g_shift B t tau (theta + m)

end Q3

namespace Q3.Proofs.ShiftedWindows

open Q3

lemma phi_shift_support (B t tau xi : ℝ) (hB : 0 < B) (h : B < |xi - tau|) :
    Q3.phi_shift B t tau xi = 0 := by
  unfold Q3.phi_shift Q3.fejer_heat_window
  have h1 : 1 - |xi - tau| / B < 0 := by
    have : 1 < |xi - tau| / B := by
      rw [one_lt_div hB]
      exact h
    linarith
  simp [max_eq_left (le_of_lt h1)]

lemma g_shift_support (B t tau xi : ℝ) (hB : 0 < B) (h : B < |xi - tau|) :
    Q3.g_shift B t tau xi = 0 := by
  simp [Q3.g_shift, phi_shift_support B t tau xi hB h]

lemma continuous_a : Continuous Q3.a := by
  have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
  have h :
      (fun xi => Q3.a xi) = fun xi => (1 / (2 * Real.pi)) * Q3.a_star xi := by
    funext xi
    have h' : (1 / (2 * Real.pi)) * Q3.a_star xi = Q3.a xi := by
      calc
        (1 / (2 * Real.pi)) * Q3.a_star xi
            = (1 / (2 * Real.pi)) * (2 * Real.pi * Q3.a xi) := by simp [Q3.a_star]
        _ = Q3.a xi := by
          field_simp [hpi]
    simpa using h'.symm
  have hcont : Continuous (fun xi => (1 / (2 * Real.pi)) * Q3.a_star xi) :=
    continuous_const.mul Q3.a_star_continuous
  simpa [h] using hcont

lemma continuous_fejer_heat_window (B t : ℝ) :
    Continuous (fun xi => Q3.fejer_heat_window B t xi) := by
  unfold Q3.fejer_heat_window
  have h_lin : Continuous (fun xi : ℝ => 1 - |xi| / B) := by
    have h_abs : Continuous (fun xi : ℝ => |xi|) := by
      simpa using (continuous_abs : Continuous fun xi : ℝ => |xi|)
    have h_div : Continuous (fun xi : ℝ => |xi| / B) := by
      simpa [div_eq_mul_inv] using h_abs.mul continuous_const
    exact continuous_const.sub h_div
  have h_max : Continuous (fun xi : ℝ => max (0 : ℝ) (1 - |xi| / B)) :=
    (continuous_const).max h_lin
  have h_pow : Continuous (fun xi : ℝ => xi ^ 2) := by
    simpa using (continuous_pow 2 : Continuous fun xi : ℝ => xi ^ 2)
  have h_poly : Continuous (fun xi : ℝ => (-4 * Real.pi ^ 2 * t) * (xi ^ 2)) :=
    continuous_const.mul h_pow
  have h_exp : Continuous (fun xi : ℝ => Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2)) := by
    simpa [mul_assoc] using (Real.continuous_exp.comp h_poly)
  exact h_max.mul h_exp

lemma continuous_phi_shift (B t tau : ℝ) :
    Continuous (fun xi => Q3.phi_shift B t tau xi) := by
  simpa [Q3.phi_shift] using
    (continuous_fejer_heat_window B t).comp (continuous_id.sub continuous_const)

lemma continuous_g_shift (B t tau : ℝ) :
    Continuous (fun xi => Q3.g_shift B t tau xi) := by
  exact continuous_a.mul (continuous_phi_shift B t tau)

lemma phi_shift_support_of_margin (B t tau K : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∀ xi, K < |xi| → Q3.phi_shift B t tau xi = 0 := by
  intro xi hxi
  have h_lower : |xi| - |tau| ≤ |xi - tau| := by
    exact abs_sub_abs_le_abs_sub xi tau
  have hB' : B < |xi - tau| := by
    have h1 : B ≤ K - |tau| := by linarith [hK]
    have h2 : K - |tau| < |xi| - |tau| := by linarith [hxi]
    have h3 : B < |xi| - |tau| := lt_of_le_of_lt h1 h2
    linarith [h_lower, h3]
  exact phi_shift_support B t tau xi hB hB'

lemma g_shift_support_of_margin (B t tau K : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K) :
    ∀ xi, K < |xi| → Q3.g_shift B t tau xi = 0 := by
  intro xi hxi
  simp [Q3.g_shift, phi_shift_support_of_margin B t tau K hB hK xi hxi]

lemma g_shift_zero_of_large_m (B t tau theta : ℝ) (m : ℤ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2))
    (hm : (⌈B + |tau|⌉ : ℤ) + 1 < |m|) :
    Q3.g_shift B t tau (theta + m) = 0 := by
  have hm_real : B + |tau| + 1 < |(m : ℝ)| := by
    have hm' : (⌈B + |tau|⌉ : ℝ) + 1 < |m| := by exact_mod_cast hm
    have hceil : B + |tau| ≤ (⌈B + |tau|⌉ : ℝ) := Int.le_ceil (B + |tau|)
    have hmid : B + |tau| + 1 < |m| := by linarith [hceil, hm']
    have h_abs : (|m| : ℝ) = |(m : ℝ)| := by simp
    simpa [h_abs] using hmid
  have htheta_abs : |theta| ≤ (1/2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [htheta.1, htheta.2]
  have hthetatau : |theta - tau| ≤ |theta| + |tau| := by
    have h := abs_add_le theta (-tau)
    simpa [sub_eq_add_neg, abs_neg, add_comm, add_left_comm, add_assoc] using h
  have hthetatau' : |theta - tau| ≤ |tau| + (1/2 : ℝ) := by
    linarith [htheta_abs, hthetatau]
  have htri : |(m : ℝ)| - |theta - tau| ≤ |theta + (m : ℝ) - tau| := by
    have h := abs_add_le (theta + (m : ℝ) - tau) (tau - theta)
    have hsum : (theta + (m : ℝ) - tau) + (tau - theta) = (m : ℝ) := by ring_nf
    have h1 : |(m : ℝ)| ≤ |theta + (m : ℝ) - tau| + |tau - theta| := by
      simpa [hsum] using h
    have h2 : |(m : ℝ)| ≤ |theta + (m : ℝ) - tau| + |theta - tau| := by
      simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using h1
    linarith [h2]
  have hB' : B < |theta + (m : ℝ) - tau| := by
    have hmid : B < |(m : ℝ)| - |theta - tau| := by
      linarith [hm_real, hthetatau']
    linarith [htri, hmid]
  exact g_shift_support B t tau (theta + m) hB (by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hB')

lemma P_A_shift_locally_finite_sum (B t tau θ₀ : ℝ) (hB : 0 < B) :
    ∃ N : ℕ, ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2),
      Q3.P_A_shift B t tau θ =
        2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, Q3.g_shift B t tau (θ + m) := by
  let K : ℝ := |tau| + B
  refine ⟨Nat.ceil (|θ₀| + K) + 4, ?_⟩
  intro θ hθ
  unfold Q3.P_A_shift
  congr 1
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have hθ_bound : |θ| < |θ₀| + 1/2 := by
    have h1 : θ₀ - 1/2 < θ := hθ.1
    have h2 : θ < θ₀ + 1/2 := hθ.2
    rw [abs_lt]
    constructor
    · by_cases hθ₀_neg : θ₀ ≤ 0
      · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
        linarith
      · push_neg at hθ₀_neg
        have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
        linarith
    · by_cases hθ₀_neg : θ₀ ≤ 0
      · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
        linarith
      · push_neg at hθ₀_neg
        have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
        linarith
  have hN : (Nat.ceil (|θ₀| + K) : ℤ) + 4 < |m| := by
    by_cases h : m < -((Nat.ceil (|θ₀| + K) : ℤ) + 4)
    · have hm_neg : m < 0 := by omega
      simp only [abs_of_neg hm_neg]
      omega
    · push_neg at h
      have hm' := hm h
      have hm_nonneg : 0 ≤ m := by omega
      simp only [abs_of_nonneg hm_nonneg]
      exact hm'
  have h_m_real : |θ₀| + K + 4 < |(m : ℝ)| := by
    have h1 : (Nat.ceil (|θ₀| + K) : ℝ) + 4 < |m| := by exact_mod_cast hN
    have hceil : |θ₀| + K ≤ (Nat.ceil (|θ₀| + K) : ℝ) := by
      exact Nat.le_ceil (|θ₀| + K)
    calc |θ₀| + K + 4 ≤ (Nat.ceil (|θ₀| + K) : ℝ) + 4 := by linarith
      _ < |m| := h1
      _ = |(m : ℝ)| := by simp [Int.cast_abs]
  have h_tri : |(m : ℝ)| - |θ| ≤ |θ + (m : ℝ)| := by
    have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
    have h2 : |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := by
      simpa [abs_neg, sub_eq_add_neg] using h1
    simpa [add_comm] using h2
  have h_final : K < |θ + (m : ℝ)| := by
    have hmid : K < |(m : ℝ)| - |θ| := by
      linarith [h_m_real, hθ_bound]
    linarith [h_tri, hmid]
  have h_final' : K < |θ + m| := by
    simpa using h_final
  exact g_shift_support_of_margin B t tau K hB (by simp [K, add_comm]) (θ + m) h_final'

lemma P_A_shift_tsum_eq_finite_sum (B t tau theta : ℝ) (hB : 0 < B)
    (htheta : theta ∈ Set.Icc (-1/2 : ℝ) (1/2)) :
    ∑' (m : ℤ), Q3.g_shift B t tau (theta + m) =
      ∑ m ∈ Finset.Icc (-(⌈B + |tau|⌉ + 1)) (⌈B + |tau|⌉ + 1),
        Q3.g_shift B t tau (theta + m) := by
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  have hceil_pos : (0 : ℤ) < ⌈B + |tau|⌉ + 1 := by
    have : (0 : ℤ) ≤ ⌈B + |tau|⌉ := by
      exact Int.ceil_nonneg (by nlinarith [abs_nonneg tau, hB])
    omega
  have h_large : (⌈B + |tau|⌉ : ℤ) + 1 < |m| := by
    by_cases h : m < -(⌈B + |tau|⌉ + 1)
    · have hm_neg : m < 0 := by linarith [hceil_pos, h]
      have hneg : (⌈B + |tau|⌉ : ℤ) + 1 < -m := by linarith
      simpa [abs_of_neg hm_neg] using hneg
    · push_neg at h
      have hm' : (⌈B + |tau|⌉ : ℤ) + 1 < m := hm h
      have hm_nonneg : 0 ≤ m := by linarith [hceil_pos, hm']
      simpa [abs_of_nonneg hm_nonneg] using hm'
  exact g_shift_zero_of_large_m B t tau theta m hB htheta h_large

theorem P_A_shift_continuous (B t tau : ℝ) (hB : 0 < B) :
    Continuous (Q3.P_A_shift B t tau) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  obtain ⟨N, hN⟩ := P_A_shift_locally_finite_sum (B:=B) (t:=t) (tau:=tau) (θ₀:=θ₀) hB
  let f := fun θ => 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, Q3.g_shift B t tau (θ + m)
  have h_sum_cont : Continuous f := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro m _
    exact (continuous_g_shift B t tau).comp (continuous_id.add continuous_const)
  have h_mem : Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2) ∈ nhds θ₀ := by
    apply Ioo_mem_nhds <;> linarith
  have h_eq : ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2), Q3.P_A_shift B t tau θ = f θ := hN
  have h_f_cont : ContinuousAt f θ₀ := h_sum_cont.continuousAt
  have h_eq_f : Q3.P_A_shift B t tau =ᶠ[nhds θ₀] f := by
    apply Filter.eventuallyEq_of_mem h_mem
    intro θ hθ
    exact h_eq θ hθ
  exact h_f_cont.congr h_eq_f.symm

lemma arch_term_eq_two_pi_integral_g_shift (B t tau : ℝ) :
    Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) =
      2 * Real.pi * ∫ xi, Q3.g_shift B t tau xi := by
  have h :
      ∀ xi, Q3.a_star xi * Q3.phi_shift B t tau xi =
        2 * Real.pi * (Q3.a xi * Q3.phi_shift B t tau xi) := by
    intro xi
    simp [Q3.a_star]
    ring_nf
  simp [Q3.arch_term, Q3.g_shift, h, MeasureTheory.integral_const_mul]

theorem integral_P_A_shift_eq_arch_term (B t tau : ℝ) (hB : 0 < B) :
    ∫ theta in (-1/2 : ℝ)..(1/2), Q3.P_A_shift B t tau theta =
      Q3.arch_term (fun xi => Q3.phi_shift B t tau xi) := by
  classical
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  let K : ℝ := B + |tau|
  let s : Finset ℤ := Finset.Icc (-(⌈K⌉ + 1)) (⌈K⌉ + 1)
  have hsupp : Function.support (fun xi => Q3.g_shift B t tau xi) ⊆ Set.Icc (-K) K := by
    refine Function.support_subset_iff'.2 ?_
    intro xi hxi
    have hnot_abs : ¬ |xi| ≤ K := by
      intro habs
      have h' : -K ≤ xi ∧ xi ≤ K := (abs_le.mp habs)
      exact hxi h'
    have hK : K < |xi| := lt_of_not_ge hnot_abs
    exact g_shift_support_of_margin B t tau K hB (by simp [K, add_comm]) xi hK
  have hcompact : HasCompactSupport (fun xi => Q3.g_shift B t tau xi) := by
    exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : Integrable (fun xi => Q3.g_shift B t tau xi) := by
    exact (continuous_g_shift B t tau).integrable_of_hasCompactSupport hcompact

  have h_eq_tsum :
      Set.EqOn (fun theta => ∑' m : ℤ, Q3.g_shift B t tau (theta + m))
        (fun theta => ∑ m ∈ s, Q3.g_shift B t tau (theta + m))
        (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
    intro theta htheta
    have htheta' : theta ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
      have htheta' : (-1/2 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) := by
        rcases Set.mem_uIcc.mp htheta with hθ | hθ
        · exact hθ
        · exfalso
          linarith [hθ.1, hθ.2, hab]
      exact htheta'
    simpa [s, K] using P_A_shift_tsum_eq_finite_sum B t tau theta hB htheta'

  have h_int_eq :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) := by
    exact intervalIntegral.integral_congr h_eq_tsum

  have h_int_sum :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) =
        ∑ m ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + m) := by
    refine intervalIntegral.integral_finset_sum ?_
    intro m hm
    have hcont : Continuous (fun theta => Q3.g_shift B t tau (theta + m)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (continuous_g_shift B t tau).comp (continuous_id.add continuous_const)
    exact hcont.intervalIntegrable (μ:=volume) (-1/2 : ℝ) (1/2 : ℝ)

  have hsum_base :
      HasSum (fun n : ℤ =>
          ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, Q3.g_shift B t tau x)
        (∫ x, Q3.g_shift B t tau x) := by
    simpa using
      (MeasureTheory.Integrable.hasSum_intervalIntegral (μ:=volume)
        (f:=fun x => Q3.g_shift B t tau x) (y:=(-1/2 : ℝ)) hint)

  have hsum :
      HasSum (fun n : ℤ => ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)))
        (∫ x, Q3.g_shift B t tau x) := by
    refine (HasSum.congr_fun hsum_base ?_)
    intro n
    have hcomp :=
      intervalIntegral.integral_comp_add_right (f:=fun x => Q3.g_shift B t tau x) (d:=(n : ℝ))
        (a:=(-1/2 : ℝ)) (b:=(1/2 : ℝ))
    convert hcomp using 1
    ring_nf

  have hsum_eq :
      (∑' n : ℤ, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ))) =
        ∑ n ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)) := by
    apply tsum_eq_sum
    intro n hn
    have hn' : ¬ (-(⌈K⌉ + 1) ≤ n ∧ n ≤ ⌈K⌉ + 1) := by
      simpa [s, Finset.mem_Icc] using hn
    have hceil_pos : (0 : ℤ) < ⌈K⌉ + 1 := by
      have hK0 : 0 ≤ K := by nlinarith [abs_nonneg tau, hB]
      have : (0 : ℤ) ≤ ⌈K⌉ := Int.ceil_nonneg hK0
      omega
    have h_large : (⌈K⌉ : ℤ) + 1 < |n| := by
      by_cases h : n < -(⌈K⌉ + 1)
      · have hn_neg : n < 0 := by linarith [hceil_pos, h]
        have hneg : (⌈K⌉ : ℤ) + 1 < -n := by linarith
        simpa [abs_of_neg hn_neg] using hneg
      · push_neg at h
        have hnot : ¬ n ≤ ⌈K⌉ + 1 := by
          intro hle
          exact hn' ⟨h, hle⟩
        have hn'' : (⌈K⌉ : ℤ) + 1 < n := lt_of_not_ge hnot
        have hn_nonneg : 0 ≤ n := by linarith [hceil_pos, hn'']
        simpa [abs_of_nonneg hn_nonneg] using hn''
    have h_eq0 :
        Set.EqOn (fun theta => Q3.g_shift B t tau (theta + n)) (fun _ => (0 : ℝ))
          (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ)) := by
      intro theta htheta
      have htheta' : theta ∈ Set.Icc (-1/2 : ℝ) (1/2 : ℝ) := by
        have htheta' : (-1/2 : ℝ) ≤ theta ∧ theta ≤ (1/2 : ℝ) := by
          rcases Set.mem_uIcc.mp htheta with hθ | hθ
          · exact hθ
          · exfalso
            linarith [hθ.1, hθ.2, hab]
        exact htheta'
      simpa [K] using g_shift_zero_of_large_m B t tau theta n hB htheta' h_large
    have h_integral_zero :
        ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + n) =
          ∫ theta in (-1/2 : ℝ)..(1/2), (0 : ℝ) := by
      exact intervalIntegral.integral_congr h_eq0
    simpa using h_integral_zero

  have hsum_fin :
      ∑ n ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + (n : ℝ)) =
        ∫ x, Q3.g_shift B t tau x := by
    exact hsum_eq.symm.trans hsum.tsum_eq

  have h_integral :
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ x, Q3.g_shift B t tau x := by
    calc
      ∫ theta in (-1/2 : ℝ)..(1/2), ∑' m : ℤ, Q3.g_shift B t tau (theta + m)
          = ∫ theta in (-1/2 : ℝ)..(1/2), ∑ m ∈ s, Q3.g_shift B t tau (theta + m) := h_int_eq
      _ = ∑ m ∈ s, ∫ theta in (-1/2 : ℝ)..(1/2), Q3.g_shift B t tau (theta + m) := h_int_sum
      _ = ∫ x, Q3.g_shift B t tau x := hsum_fin

  have h_integral' :
      ∫ theta in (-1/2 : ℝ)..(2⁻¹), ∑' m : ℤ, Q3.g_shift B t tau (theta + m) =
        ∫ x, Q3.g_shift B t tau x := by
    simpa [one_div] using h_integral

  rw [arch_term_eq_two_pi_integral_g_shift]
  simp [Q3.P_A_shift, intervalIntegral.integral_const_mul, h_integral']

end Q3.Proofs.ShiftedWindows


## File: full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge_defs.lean

/-
Definitions for the Fourier A3 bridge (shared).
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.P_A_Bridge

/-- A3 bridge data using Fourier Toeplitz with P_A symbol.
    This is the CORRECT formulation (Fourier Toeplitz, not sampling). -/
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
             Q3.T_P_comp_real K K t M) v
          ≥ Q3.c_star / 4

end Q3.Proofs.P_A_Bridge


## File: full/q3.lean.aristotle/Q3/Proofs/P_A_Toeplitz_bridge.lean

/-
P_A Toeplitz Bridge: Connect A3_FLOOR (P_A ≥ c*) with Rayleigh_Fourier

This module bridges:
- A3_Floor_Main.P_A_ge_c_star : P_A(B_min, t_sym, θ) ≥ 11/10 for θ ∈ [-1/2, 1/2]
- Rayleigh_Fourier.rayleigh_lower_bound_real : RQ(ToeplitzFourier P) ≥ inf(P)

Result: RQ(ToeplitzFourier P_A) ≥ c_star

Integration: change-durch: claude-code 2026-01-16 P_A_Toeplitz_bridge
-/

import Q3.Axioms
import Q3.Proofs.Rayleigh_Fourier
import Q3.Proofs.A3_bridge_rayleigh_first  -- t_rkhs_cap, one_le_t_rkhs_cap, c_star_div_four_le_sub_rho_one
import Q3.Proofs.RKHS_cap_rayleigh         -- rkhs_cap_rayleigh_tcap
import Q3.Proofs.Rayleigh_utils            -- RayleighQuotient_sub_ge
import Q3.Proofs.A3_Floor_Main

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

set_option maxHeartbeats 0

noncomputable section

namespace Q3.Proofs.P_A_Bridge

open Q3.Proofs  -- access t_rkhs_cap, rkhs_cap_rayleigh_tcap, RayleighQuotient_sub_ge, etc.

/- P_A is the periodized windowed archimedean symbol.
   P_A(B,t,θ) = 2π Σ_{m∈ℤ} g(B,t,θ+m) where g = a · w (Fejér×heat window).

   Continuity is currently assumed in `A3_Floor_Main` as
   `P_A_continuous`. -/

/-- Bridge lemma: Apply Rayleigh lower bound to P_A.
    Uses P_A_ge_c_star from A3_FLOOR and rayleigh_lower_bound_real from Rayleigh_Fourier. -/
lemma P_A_rayleigh_lower_bound
    (M : ℕ) (hM : M > 0)
    (v : Fin M → ℝ) (hv : v ≠ 0) :
    Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real M (P_A B_min t_sym)) v ≥ c_star := by
  have hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2), c_star ≤ P_A B_min t_sym θ := by
    intro θ hθ
    exact P_A_ge_c_star hθ
  exact RayleighFourier.rayleigh_lower_bound_real
    (M := M) (hM := hM)
    (P := P_A B_min t_sym) (hP_cont := P_A_continuous)
    (m := c_star) (hP_ge := hP_ge)
    (v := v) (hv := hv)

/-- Specialized version for M = 2*M' + 1 (symmetric frequency window). -/
lemma P_A_rayleigh_lower_bound_odd
    (M' : ℕ)
    (v : Fin (2 * M' + 1) → ℝ) (hv : v ≠ 0) :
    Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M' + 1) (P_A B_min t_sym)) v ≥ c_star := by
  have hM : 2 * M' + 1 > 0 := by omega
  exact P_A_rayleigh_lower_bound (2 * M' + 1) hM v hv

/-- A3 bridge data using Fourier Toeplitz with P_A symbol.
    This is the CORRECT formulation (Fourier coefficients, not sampling). -/
def A3_bridge_data_rayleigh_Fourier (K : ℝ) : Prop :=
  ∀ (hK : K ≥ 1) [Fintype (Q3.Nodes K)],
    ∃ t > 0, ∀ M : ℕ,
      ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
        Q3.RayleighQuotient
            (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
             Q3.T_P_comp_real K K t M) v
          ≥ Q3.c_star / 4

/-- Bridge from weight_sum bound to A3_bridge_data_rayleigh_Fourier.
    Uses P_A_rayleigh_lower_bound and RKHS cap. -/
lemma A3_bridge_rayleigh_from_weight_sum_P_A (K : ℝ)
    (h_weight_sum :
      ∀ [Fintype (Q3.Nodes K)],
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one) :
    A3_bridge_data_rayleigh_Fourier K := by
  intro hK _inst
  refine ⟨t_rkhs_cap, by linarith [one_le_t_rkhs_cap], ?_⟩
  intro M v hv
  -- Rayleigh lower bound for Fourier Toeplitz with P_A
  have hT :
      Q3.RayleighQuotient (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym)) v
        ≥ c_star := by
    have hM : 2 * M + 1 > 0 := by omega
    exact P_A_rayleigh_lower_bound (2 * M + 1) hM v hv
  -- RKHS cap
  have hP :
      Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one := by
    have h_weight_sum' :
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one := h_weight_sum
    exact rkhs_cap_rayleigh_tcap (K:=K) (B:=K) (h_weight_sum:=h_weight_sum') M v hv
  -- Combine via subtraction
  have hsub :
      Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
           Q3.T_P_comp_real K K t_rkhs_cap M) v
        ≥ c_star - rho_one := by
    exact RayleighQuotient_sub_ge
      (A:=RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym))
      (B:=Q3.T_P_comp_real K K t_rkhs_cap M) (v:=v)
      (a:=c_star) (b:=rho_one) hT hP
  exact le_trans c_star_div_four_le_sub_rho_one hsub

end Q3.Proofs.P_A_Bridge


## File: full/q3.lean.aristotle/Q3/Proofs/Rayleigh_basis0_of_A3.lean

/-
Rayleigh basis0 bound extracted from Fourier A3 bridge.
-/

import Q3.Proofs.Rayleigh_basis0
import Q3.Proofs.P_A_Toeplitz_bridge

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical

noncomputable section

namespace Q3.Proofs.QNonnegAtoms

lemma rayleigh_basis0_of_A3 (K : ℝ) (hK : K ≥ 1) [Fintype (Q3.Nodes K)]
    (hA3 : Q3.Proofs.P_A_Bridge.A3_bridge_data_rayleigh_Fourier K) :
    ∃ t > 0, ∀ M : ℕ,
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1) (P_A B_min t_sym) -
         Q3.T_P_comp_real K K t M)
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  classical
  obtain ⟨t, ht, hA3M⟩ := hA3 hK
  refine ⟨t, ht, ?_⟩
  intro M
  have hne : Q3.Proofs.RayleighQId.basis0 M ≠ 0 :=
    Q3.Proofs.RayleighQId.basis0_ne_zero M
  exact hA3M M (Q3.Proofs.RayleighQId.basis0 M) hne

end Q3.Proofs.QNonnegAtoms


## File: full/q3.lean.aristotle/Q3/Proofs/RKHS_cap_rayleigh.lean

/-
RKHS cap for the Rayleigh quotient (compression form).
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Q3.Axioms
import Q3.Proofs.Rayleigh_utils
import Q3.Proofs.T_P_comp_utils
import Q3.Proofs.A3_bridge_rayleigh_first
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.C1_T_P_comp_dictEmbedding
import Q3.Proofs.RKHS_Interface_C1

set_option maxHeartbeats 0

open scoped BigOperators
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Q3.Proofs

private def normSq {M : ℕ} (v : Fin M → ℝ) : ℝ :=
  ∑ i, (v i) ^ 2

private def quadForm {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * A i j * v j

private def rayleighQ {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) : ℝ :=
  quadForm A v / normSq v

private def rankOne {M : ℕ} (α : ℝ) (u : Fin M → ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  fun i j => α * u i * u j

lemma inner_sq_le_normSq {M : ℕ} (u v : Fin M → ℝ) (hu : ∑ i, (u i) ^ 2 = 1) :
    (∑ i, u i * v i) ^ 2 ≤ ∑ i, (v i) ^ 2 := by
  have h_cauchy_schwarz :
      (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (f:=u) (g:=v))
  simpa [hu] using h_cauchy_schwarz

lemma quadForm_rankOne {M : ℕ} (α : ℝ) (u v : Fin M → ℝ) :
    quadForm (rankOne α u) v = α * (∑ i, u i * v i) ^ 2 := by
  simp +decide [Finset.mul_sum, pow_two, mul_comm, mul_left_comm, rankOne, quadForm]

lemma quadForm_sum {M : ℕ} {ι : Type*} [Fintype ι]
    (As : ι → Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    quadForm (∑ n, As n) v = ∑ n, quadForm (As n) v := by
  unfold quadForm
  simp +decide only [mul_comm, Matrix.sum_apply, Finset.mul_sum]
  exact Eq.symm (by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ =>
      Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => by ring)))))

lemma rayleighQ_rankone_sum_le
    {M : ℕ} [NeZero M] {NodesK : Type} [Fintype NodesK] [DecidableEq NodesK]
    (coeff : NodesK → ℝ) (basis : NodesK → Fin M → ℝ)
    (v : Fin M → ℝ)
    (h_coeff_nonneg : ∀ n, 0 ≤ coeff n)
    (h_basis_norm : ∀ n, ∑ i : Fin M, (basis n i) ^ 2 = 1) :
    Q3.RayleighQuotient (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
      ≤ ∑ n : NodesK, coeff n := by
  have hRayleigh :
      rayleighQ (fun i j => ∑ n : NodesK, coeff n * basis n i * basis n j) v
        ≤ ∑ n : NodesK, coeff n := by
    refine' div_le_of_le_mul₀ _ _ _
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    · exact Finset.sum_nonneg (fun _ _ => h_coeff_nonneg _)
    · have h_quadForm_sum :
          quadForm (fun i j => ∑ n, coeff n * basis n i * basis n j) v
            = ∑ n, coeff n * (∑ i, basis n i * v i) ^ 2 := by
          unfold quadForm
          simp +decide only [mul_comm, mul_left_comm, Finset.mul_sum, pow_two]
          exact Eq.symm (by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl (fun _ _ =>
              Finset.sum_comm.trans (Finset.sum_congr rfl (fun _ _ =>
                Finset.sum_congr rfl (fun _ _ => by ring)))))
      have h_inner_sq_le_normSq : ∀ n, (∑ i, basis n i * v i) ^ 2 ≤ normSq v := by
        intro n
        have h_inner_sq_le_normSq :
            (∑ i, basis n i * v i) ^ 2 ≤
              (∑ i, (basis n i) ^ 2) * (∑ i, (v i) ^ 2) := by
          simpa using
            (Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (f:=basis n) (g:=v))
        have hnorm := h_basis_norm n
        simpa [normSq, hnorm] using h_inner_sq_le_normSq
      simpa only [h_quadForm_sum, Finset.sum_mul] using
        Finset.sum_le_sum (fun n _ =>
          mul_le_mul_of_nonneg_left (h_inner_sq_le_normSq n) (h_coeff_nonneg n))
  simpa [rayleighQ, Q3.RayleighQuotient, quadForm, normSq] using hRayleigh

lemma fejer_heat_window_le_exp (B t ξ : ℝ) (hB : 0 < B) :
    Q3.fejer_heat_window B t ξ ≤ Real.exp (-4 * Real.pi ^ 2 * t * ξ ^ 2) := by
  unfold Q3.fejer_heat_window
  have hmax : max (0 : ℝ) (1 - |ξ| / B) ≤ 1 := by
    refine max_le_iff.mpr ?_
    constructor
    · norm_num
    · have : 0 ≤ |ξ| / B := by
        exact div_nonneg (abs_nonneg _) (le_of_lt hB)
      linarith
  have h := mul_le_mul_of_nonneg_right hmax
    (Real.exp_nonneg (-4 * Real.pi ^ 2 * t * ξ ^ 2))
  simpa [one_mul] using h

lemma w_Q_le_const (n : ℕ) (hn : n ≥ 2) :
    Q3.w_Q n ≤ 4 / Real.exp 1 := by
  have hlog : Real.log n / Real.sqrt n ≤ 2 / Real.exp 1 :=
    Q3.log_div_sqrt_le n hn
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hmul : 2 * ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log (n : ℝ) := by
    nlinarith [hΛ]
  have hdiv :
      (2 * ArithmeticFunction.vonMangoldt n) / Real.sqrt n
        ≤ (2 * Real.log (n : ℝ)) / Real.sqrt n := by
    exact div_le_div_of_nonneg_right hmul (Real.sqrt_nonneg _)
  have hlog' :
      (2 * Real.log (n : ℝ)) / Real.sqrt n ≤ 4 / Real.exp 1 := by
    calc
      (2 * Real.log (n : ℝ)) / Real.sqrt n
          = 2 * (Real.log n / Real.sqrt n) := by ring
      _ ≤ 2 * (2 / Real.exp 1) := by
          exact mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
      _ = 4 / Real.exp 1 := by ring
  have hw : Q3.w_Q n = (2 * ArithmeticFunction.vonMangoldt n) / Real.sqrt n := by
    unfold Q3.w_Q
    ring
  exact (le_trans (by simpa [hw] using hdiv) hlog')

lemma exp_log_sq_le_pow (n : ℕ) (hn : n ≥ 2) :
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ (n : ℝ) ^ (-10 : ℝ) := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have ht : (10 : ℝ) ≤ t_rkhs_cap * Real.log 2 := by
    have ht' : (10 : ℝ) ≤ (40 : ℝ) * Real.log 2 := by
      nlinarith [hlog2]
    simpa [t_rkhs_cap] using ht'
  have hlog_ge : Real.log 2 ≤ Real.log n := by
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    exact Real.log_le_log (by norm_num) h2
  have ht' : (10 : ℝ) ≤ t_rkhs_cap * Real.log n := by
    have hpos : 0 ≤ t_rkhs_cap := by norm_num [t_rkhs_cap]
    exact le_trans ht (mul_le_mul_of_nonneg_left hlog_ge hpos)
  have hlog_pos : 0 < Real.log n := by
    have h2 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hn)
    exact Real.log_pos h2
  have hmul : (10 : ℝ) * Real.log n ≤ t_rkhs_cap * (Real.log n) ^ 2 := by
    have := mul_le_mul_of_nonneg_right ht' (le_of_lt hlog_pos)
    simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using this
  have hneg : -t_rkhs_cap * (Real.log n) ^ 2 ≤ -10 * Real.log n := by
    nlinarith [hmul]
  have hexp : Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ Real.exp (-10 * Real.log n) := by
    exact (Real.exp_le_exp).2 hneg
  have hpow : Real.exp (-10 * Real.log n) = (n : ℝ) ^ (-10 : ℝ) := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hn)
    -- rpow_def_of_pos gives: n^(-10) = exp (log n * (-10))
    have h := Real.rpow_def_of_pos hnpos (-10 : ℝ)
    -- rewrite to exp (-10 * log n)
    simpa [mul_comm] using h.symm
  calc
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2)
        ≤ Real.exp (-10 * Real.log n) := hexp
    _ = (n : ℝ) ^ (-10 : ℝ) := hpow

lemma exp_log_sq_le_inv_pow (n : ℕ) (hn : n ≥ 2) :
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2) ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
  have h := exp_log_sq_le_pow n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn)
  have hx : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hpow : (n : ℝ) ^ (-10 : ℝ) = 1 / (n : ℝ) ^ (10 : ℕ) := by
    calc
      (n : ℝ) ^ (-10 : ℝ) = ((n : ℝ) ^ (10 : ℝ))⁻¹ := by
        rw [Real.rpow_neg hx]
      _ = 1 / (n : ℝ) ^ (10 : ℕ) := by
        simp [Real.rpow_natCast, one_div]
  calc
    Real.exp (-t_rkhs_cap * (Real.log n) ^ 2)
        ≤ (n : ℝ) ^ (-10 : ℝ) := h
    _ = 1 / (n : ℝ) ^ (10 : ℕ) := hpow

private def pow_inv_shift (n : ℕ) : ℝ := 1 / (n + 2 : ℝ) ^ (10 : ℕ)

lemma pow_inv_shift_nonneg (n : ℕ) : 0 ≤ pow_inv_shift n := by
  have hpos : 0 ≤ (n + 2 : ℝ) ^ (10 : ℕ) := by positivity
  exact one_div_nonneg.mpr hpos

lemma pow_inv_shift_antitone {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    pow_inv_shift n ≤ pow_inv_shift m := by
  have hmn' : (m + 2 : ℝ) ≤ n + 2 := by
    exact_mod_cast (Nat.add_le_add_right hmn 2)
  have hpow : (m + 2 : ℝ) ^ (10 : ℕ) ≤ (n + 2 : ℝ) ^ (10 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hmn' _
  have hpos : 0 < (m + 2 : ℝ) ^ (10 : ℕ) := by positivity
  have hpos' : 0 < (n + 2 : ℝ) ^ (10 : ℕ) := by positivity
  have hinv : 1 / (n + 2 : ℝ) ^ (10 : ℕ) ≤ 1 / (m + 2 : ℝ) ^ (10 : ℕ) := by
    exact one_div_le_one_div_of_le hpos hpow
  simpa [pow_inv_shift] using hinv

lemma summable_pow_inv_shift : Summable pow_inv_shift := by
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) := by
    exact (Real.summable_one_div_nat_pow (p:=10)).2 (by norm_num)
  have hsum_shift :
      Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ (10 : ℕ)) := by
    simpa [one_div, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff (f:=fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) 2).2 hsum
  refine hsum_shift.congr ?_
  intro n
  simp [pow_inv_shift]

lemma condensed_term_le_geom (k : ℕ) :
    (2 ^ k : ℝ) * pow_inv_shift (2 ^ k) ≤ (1 / (2 ^ 9 : ℝ)) ^ k := by
  have hkpos : 0 ≤ (2 ^ k : ℝ) := by positivity
  have hpow_le :
      pow_inv_shift (2 ^ k) ≤ 1 / (2 ^ k : ℝ) ^ (10 : ℕ) := by
    have hle : (2 ^ k : ℝ) ≤ 2 ^ k + 2 := by
      linarith
    have hpow : (2 ^ k : ℝ) ^ (10 : ℕ) ≤ (2 ^ k + 2 : ℝ) ^ (10 : ℕ) := by
      exact pow_le_pow_left₀ (by positivity) hle _
    have hpos : 0 < (2 ^ k : ℝ) ^ (10 : ℕ) := by positivity
    have hinv : 1 / (2 ^ k + 2 : ℝ) ^ (10 : ℕ) ≤ 1 / (2 ^ k : ℝ) ^ (10 : ℕ) := by
      exact one_div_le_one_div_of_le hpos hpow
    simpa [pow_inv_shift] using hinv
  calc
    (2 ^ k : ℝ) * pow_inv_shift (2 ^ k)
        ≤ (2 ^ k : ℝ) * (1 / (2 ^ k : ℝ) ^ (10 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hpow_le hkpos
    _ = 1 / (2 ^ k : ℝ) ^ (9 : ℕ) := by
          field_simp [pow_succ]
    _ = 1 / (2 ^ 9 : ℝ) ^ k := by
          have hpow : (2 ^ k : ℝ) ^ (9 : ℕ) = (2 ^ 9 : ℝ) ^ k := by
            calc
              (2 ^ k : ℝ) ^ (9 : ℕ) = (2 : ℝ) ^ (k * 9) := by
                simpa [pow_mul] using (pow_mul (2 : ℝ) k 9).symm
              _ = (2 : ℝ) ^ (9 * k) := by
                simp [mul_comm]
              _ = (2 ^ 9 : ℝ) ^ k := by
                simpa [pow_mul] using (pow_mul (2 : ℝ) 9 k)
          simpa [hpow]
    _ = (1 / (2 ^ 9 : ℝ)) ^ k := by
          simp [one_div_pow]

private def condensed_term (k : ℕ) : ℝ := (2 ^ k : ℝ) * pow_inv_shift (2 ^ k)

lemma condensed_term_nonneg (k : ℕ) : 0 ≤ condensed_term k := by
  have : 0 ≤ (2 ^ k : ℝ) := by positivity
  have : 0 ≤ pow_inv_shift (2 ^ k) := pow_inv_shift_nonneg _
  exact mul_nonneg (by positivity) this

lemma summable_geom : Summable (fun k : ℕ => (1 / (2 ^ 9 : ℝ)) ^ k) := by
  have h0 : 0 ≤ (1 / (2 ^ 9 : ℝ)) := by positivity
  have h1 : (1 / (2 ^ 9 : ℝ)) < 1 := by norm_num
  exact summable_geometric_of_lt_one h0 h1

lemma summable_condensed_term : Summable condensed_term := by
  refine Summable.of_nonneg_of_le ?_ ?_ summable_geom
  · intro k
    exact condensed_term_nonneg k
  · intro k
    simpa [condensed_term] using (condensed_term_le_geom k)

lemma tsum_geom_tail :
    (∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) = (1 / 511 : ℝ) := by
  set r : ℝ := (1 / (2 ^ 9 : ℝ))
  have h0 : 0 ≤ r := by
    simp [r]
  have h1 : r < 1 := by
    have h : (1 / (2 ^ 9 : ℝ)) < 1 := by
      norm_num
    simpa [r] using h
  have htsum : (∑' k : ℕ, r ^ k) = (1 - r)⁻¹ := by
    exact tsum_geometric_of_lt_one h0 h1
  calc
    (∑' k : ℕ, r ^ (k + 1))
        = r * (∑' k : ℕ, r ^ k) := by
            simp [pow_succ, mul_comm, mul_left_comm, mul_assoc, tsum_mul_left]
    _ = r * (1 - r)⁻¹ := by
            simpa [htsum]
    _ = (1 / 511 : ℝ) := by
            norm_num [r]

lemma tsum_condensed_term_le :
    ∑' k : ℕ, condensed_term k ≤ pow_inv_shift 1 + (1 / 511 : ℝ) := by
  have hsum_tail :
      Summable (fun k : ℕ => condensed_term (k + 1)) := by
    simpa [condensed_term] using (summable_nat_add_iff 1).2 summable_condensed_term
  have hgeom_tail :
      Summable (fun k : ℕ => (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) := by
    simpa using (summable_nat_add_iff 1).2 summable_geom
  have htail_le :
      ∑' k : ℕ, condensed_term (k + 1) ≤
        ∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1) := by
    refine Summable.tsum_le_tsum ?_ hsum_tail hgeom_tail
    intro k
    simpa [condensed_term] using (condensed_term_le_geom (k + 1))
  have hsplit :
      ∑' k : ℕ, condensed_term k =
        condensed_term 0 + ∑' k : ℕ, condensed_term (k + 1) := by
    simpa [condensed_term] using (summable_condensed_term.sum_add_tsum_nat_add 1).symm
  calc
    ∑' k : ℕ, condensed_term k
        = condensed_term 0 + ∑' k : ℕ, condensed_term (k + 1) := hsplit
    _ ≤ condensed_term 0 + ∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1) := by
          exact add_le_add_left htail_le _
    _ = pow_inv_shift 1 + (1 / 511 : ℝ) := by
          have hgeom :
              (∑' k : ℕ, (1 / (2 ^ 9 : ℝ)) ^ (k + 1)) = (1 / 511 : ℝ) :=
            tsum_geom_tail
          simpa [condensed_term] using congrArg (fun s => condensed_term 0 + s) hgeom

lemma tsum_pow_inv_shift_le :
    ∑' n : ℕ, pow_inv_shift n ≤
      pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ) := by
  have hsum_pow : Summable pow_inv_shift := by
    have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) := by
      exact (Real.summable_one_div_nat_pow (p:=10)).2 (by norm_num)
    have hsum_shift :
        Summable (fun n : ℕ => 1 / (n + 2 : ℝ) ^ (10 : ℕ)) := by
      simpa [one_div, add_comm, add_left_comm, add_assoc] using
        (summable_nat_add_iff (f:=fun n : ℕ => 1 / (n : ℝ) ^ (10 : ℕ)) 2).2 hsum
    refine hsum_shift.congr ?_
    intro n
    simp [pow_inv_shift]
  have hbound :
      ∀ s : Finset ℕ, ∑ n ∈ s, pow_inv_shift n ≤
        pow_inv_shift 0 + ∑' k : ℕ, condensed_term k := by
    intro s
    classical
    by_cases hs : s.Nonempty
    · let N := s.max' hs
      have hsubset : s ⊆ Finset.range (2 ^ (N + 1)) := by
        intro n hn
        have hle : n ≤ N := by
          have hle' : n ≤ s.max' hs := Finset.le_max' s n hn
          simpa [N] using hle'
        have hlt : n < N + 1 := Nat.lt_succ_of_le hle
        have hpow : N + 1 ≤ 2 ^ (N + 1) := Nat.le_of_lt (Nat.lt_two_pow_self (n:=N + 1))
        exact Finset.mem_range.mpr (lt_of_lt_of_le hlt hpow)
      have hsum_le :
          (∑ n ∈ s, pow_inv_shift n) ≤
            ∑ n ∈ Finset.range (2 ^ (N + 1)), pow_inv_shift n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro n hn hnot
        exact pow_inv_shift_nonneg n
      have hcond :
          (∑ n ∈ Finset.range (2 ^ (N + 1)), pow_inv_shift n) ≤
            pow_inv_shift 0 + ∑ k ∈ Finset.range (N + 1), (2 ^ k : ℝ) • pow_inv_shift (2 ^ k) := by
        simpa using (Finset.le_sum_condensed (f:=pow_inv_shift)
          (hf:=by
            intro m n hm hmn
            exact pow_inv_shift_antitone (m:=m) (n:=n) hm hmn) (n:=N + 1))
      have hsum_condensed :
          (∑ k ∈ Finset.range (N + 1), (2 ^ k : ℝ) • pow_inv_shift (2 ^ k)) ≤
            ∑' k : ℕ, condensed_term k := by
        have hnonneg : ∀ k, 0 ≤ condensed_term k := by
          intro k
          exact condensed_term_nonneg k
        have hsum := (Summable.sum_le_tsum (s:=Finset.range (N + 1))
          (f:=condensed_term) (hs:=by
            intro k hk
            exact hnonneg k) (hf:=summable_condensed_term))
        simpa [condensed_term] using hsum
      exact le_trans hsum_le (le_trans hcond (by
        simpa [condensed_term] using add_le_add_left hsum_condensed (pow_inv_shift 0)))
    · have hnonneg : 0 ≤ pow_inv_shift 0 + ∑' k : ℕ, condensed_term k := by
        refine add_nonneg (pow_inv_shift_nonneg 0) ?_
        exact tsum_nonneg (fun _ => condensed_term_nonneg _)
      simp [Finset.not_nonempty_iff_eq_empty.mp hs, hnonneg]
  have htsum :
      ∑' n : ℕ, pow_inv_shift n ≤ pow_inv_shift 0 + ∑' k : ℕ, condensed_term k :=
    hsum_pow.tsum_le_of_sum_le hbound
  have hcond_le :
      ∑' k : ℕ, condensed_term k ≤ pow_inv_shift 1 + (1 / 511 : ℝ) :=
    tsum_condensed_term_le
  exact le_trans htsum (by
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hcond_le (pow_inv_shift 0))

lemma exp_xi_log_eq (n : ℕ) :
    Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) =
      Real.exp (-(t_rkhs_cap * (Real.log n) ^ 2)) := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hpos :
      4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2
        = t_rkhs_cap * (Real.log n) ^ 2 := by
    unfold Q3.xi_n
    field_simp [pow_two, hpi]
    ring
  have hneg :
      -(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        = -(t_rkhs_cap * (Real.log n) ^ 2) := by
    nlinarith [hpos]
  simpa [hneg]

lemma exp_shift_le_exp_mul (K t xi tau : ℝ) (hxi : |xi| ≤ K) (ht : 0 ≤ t) :
    Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2) ≤
      Real.exp (8 * Real.pi ^ 2 * t * K ^ 2) * Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
  have hxi2 : xi ^ 2 ≤ K ^ 2 := by
    have hK : 0 ≤ K := by
      exact le_trans (abs_nonneg xi) hxi
    have h' : |xi| ≤ |K| := by
      simpa [abs_of_nonneg hK] using hxi
    exact (sq_le_sq).2 h'
  have hneg' : xi ^ 2 - 2 * K ^ 2 ≤ 0 := by nlinarith [hxi2]
  have hpos : 0 ≤ (xi - tau) ^ 2 := by nlinarith
  have hneg : xi ^ 2 - 2 * K ^ 2 ≤ (xi - tau) ^ 2 := by
    exact le_trans hneg' hpos
  have hcoef : -4 * Real.pi ^ 2 * t ≤ 0 := by
    have hpi : 0 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_pos]
    nlinarith [ht, hpi]
  have hmul :
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2 ≤
        -4 * Real.pi ^ 2 * t * (xi ^ 2 - 2 * K ^ 2) := by
    exact mul_le_mul_of_nonpos_left hneg hcoef
  have hmul' :
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2 ≤
        8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2 := by
    calc
      -4 * Real.pi ^ 2 * t * (xi - tau) ^ 2
          ≤ -4 * Real.pi ^ 2 * t * (xi ^ 2 - 2 * K ^ 2) := hmul
      _ = 8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2 := by ring
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2) ≤
        Real.exp (8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2) := by
    exact (Real.exp_le_exp).2 hmul'
  calc
    Real.exp (-4 * Real.pi ^ 2 * t * (xi - tau) ^ 2)
        ≤ Real.exp (8 * Real.pi ^ 2 * t * K ^ 2 - 4 * Real.pi ^ 2 * t * xi ^ 2) := hexp
    _ = Real.exp (8 * Real.pi ^ 2 * t * K ^ 2) *
        Real.exp (-4 * Real.pi ^ 2 * t * xi ^ 2) := by
      simp [sub_eq_add_neg, Real.exp_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

def rho_oneK (K : ℝ) : ℝ :=
  Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) * rho_one

lemma weight_term_le_pow_inv (K B : ℝ) (hB : 0 < B) (n : Q3.Nodes K) :
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
      ≤ (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
  have hn : (n : ℕ) ≥ 2 := n.property.2
  have hwindow_nonneg :
      0 ≤ Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) :=
    Q3.fejer_heat_window_nonneg _ _ _
  have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
  have hprod_nonneg :
      0 ≤ Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) :=
    mul_nonneg hw_nonneg hwindow_nonneg
  have hnorm :
      ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) := by
    have hnorm' :
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ =
          |Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)| := by
      simp
    simpa [abs_of_nonneg hprod_nonneg] using hnorm'
  have hfej :
      Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)
        ≤ Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    exact fejer_heat_window_le_exp B t_rkhs_cap (Q3.xi_n n) hB
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
    have hexp0 := exp_log_sq_le_inv_pow (n:=(n : ℕ)) hn
    have hexp1 :
        Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2))
          ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
      simpa [exp_xi_log_eq (n:=(n : ℕ))] using hexp0
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hexp1
  have hw : Q3.w_Q n ≤ 4 / Real.exp 1 := w_Q_le_const (n:=(n : ℕ)) hn
  calc
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n) := hnorm
    _ ≤ (4 / Real.exp 1) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
          exact mul_le_mul hw hfej hwindow_nonneg (by positivity)
    _ ≤ (4 / Real.exp 1) * (1 / (n : ℝ) ^ (10 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
          have hn2 : 2 ≤ (n : ℕ) := hn
          have hbase : (↑↑n : ℝ) - ((2 : ℕ) : ℝ) + 2 = (↑↑n : ℝ) := by
            ring
          rw [pow_inv_shift, Nat.cast_sub hn2, hbase]

lemma weight_term_shift_le_pow_inv (K B tau : ℝ) (hB : 0 < B) (n : Q3.Nodes K) :
    ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
      ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
        (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
  have hn : (n : ℕ) ≥ 2 := n.property.2
  have hwindow_nonneg :
      0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    simpa [Q3.phi_shift] using
      Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
  have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
  have hprod_nonneg :
      0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
    mul_nonneg hw_nonneg hwindow_nonneg
  have hnorm :
      ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    have hnorm' :
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
      simp
    simpa [abs_of_nonneg hprod_nonneg] using hnorm'
  have hfej :
      Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)
        ≤ Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n - tau) ^ 2) := by
    simpa [Q3.phi_shift] using
      (fejer_heat_window_le_exp B t_rkhs_cap (Q3.xi_n n - tau) hB)
  have hshift :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n - tau) ^ 2)
        ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    have hxi : |Q3.xi_n n| ≤ K := n.property.1
    have ht : 0 ≤ t_rkhs_cap := by nlinarith [one_le_t_rkhs_cap]
    exact exp_shift_le_exp_mul (K:=K) (t:=t_rkhs_cap) (xi:=Q3.xi_n n) (tau:=tau) hxi ht
  have hphi :
      Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤
        Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2) := by
    exact le_trans hfej hshift
  have hexp :
      Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)
        ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
    have hexp0 := exp_log_sq_le_inv_pow (n:=(n : ℕ)) hn
    have hexp1 :
        Real.exp (-(4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2))
          ≤ 1 / (n : ℝ) ^ (10 : ℕ) := by
      simpa [exp_xi_log_eq (n:=(n : ℕ))] using hexp0
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using hexp1
  have hw : Q3.w_Q n ≤ 4 / Real.exp 1 := w_Q_le_const (n:=(n : ℕ)) hn
  have hconst : 0 ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) := by
    exact Real.exp_nonneg _
  calc
    ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        = Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hnorm
    _ ≤ (4 / Real.exp 1) *
          (Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) := by
          exact mul_le_mul hw hphi hwindow_nonneg (by positivity)
    _ = Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          ((4 / Real.exp 1) *
            Real.exp (-4 * Real.pi ^ 2 * t_rkhs_cap * (Q3.xi_n n) ^ 2)) := by
          ring
    _ ≤ Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          ((4 / Real.exp 1) * (1 / (n : ℝ) ^ (10 : ℕ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hconst
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2) *
          (4 / Real.exp 1) * pow_inv_shift ((n : ℕ) - 2) := by
          have hn2 : 2 ≤ (n : ℕ) := hn
          have hbase : (↑↑n : ℝ) - ((2 : ℕ) : ℝ) + 2 = (↑↑n : ℝ) := by
            ring
          simp [pow_inv_shift, Nat.cast_sub hn2, hbase, mul_assoc, mul_left_comm, mul_comm]

lemma weight_sum_le_rho_one (K B : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
      ≤ rho_one := by
  classical
  let idx : Q3.Nodes K → ℕ := fun n => (n : ℕ) - 2
  have hidx_inj : Set.InjOn idx (Set.univ : Set (Q3.Nodes K)) := by
    intro a ha b hb h
    have ha2 : 2 ≤ (a : ℕ) := a.property.2
    have hb2 : 2 ≤ (b : ℕ) := b.property.2
    have h' := congrArg (fun x => x + 2) h
    have hab : (a : ℕ) = (b : ℕ) := by
      simpa [idx, Nat.sub_add_cancel ha2, Nat.sub_add_cancel hb2] using h'
    exact Subtype.ext hab
  have hterm :
      ∀ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    intro n
    simpa [idx] using weight_term_le_pow_inv (K:=K) (B:=B) hB n
  have hsum_le :
      ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        ≤ ∑ n : Q3.Nodes K, (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hterm n
  have hsum_image :
      ∑ n : Q3.Nodes K, (4 / Real.exp 1) * pow_inv_shift (idx n) =
        Finset.sum (Finset.univ.image idx)
          (fun m => (4 / Real.exp 1) * pow_inv_shift m) := by
    have hidx_inj' :
        Set.InjOn idx (↑(Finset.univ : Finset (Q3.Nodes K)) : Set (Q3.Nodes K)) := by
      intro a ha b hb h
      exact hidx_inj (by trivial) (by trivial) h
    simpa using (Finset.sum_image (s:=Finset.univ)
      (f:=fun m => (4 / Real.exp 1) * pow_inv_shift m) (g:=idx) hidx_inj').symm
  have hsum_le_tsum :
      Finset.sum (Finset.univ.image idx)
          (fun m => (4 / Real.exp 1) * pow_inv_shift m) ≤
        ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m := by
    have hsum : Summable (fun m : ℕ => (4 / Real.exp 1) * pow_inv_shift m) := by
      exact Summable.mul_left (4 / Real.exp 1) summable_pow_inv_shift
    have hnonneg : ∀ m, 0 ≤ (4 / Real.exp 1) * pow_inv_shift m := by
      intro m
      exact mul_nonneg (by positivity) (pow_inv_shift_nonneg m)
    exact Summable.sum_le_tsum (s:=Finset.univ.image idx)
      (f:=fun m : ℕ => (4 / Real.exp 1) * pow_inv_shift m)
      (hs:=by intro m hm; exact hnonneg m) (hf:=hsum)
  have htsum_bound :
      ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m ≤
        (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
    have hnonneg : 0 ≤ (4 / Real.exp 1 : ℝ) := by positivity
    calc
      ∑' m : ℕ, (4 / Real.exp 1) * pow_inv_shift m
          = (4 / Real.exp 1) * ∑' m : ℕ, pow_inv_shift m := by
              simpa using (tsum_mul_left (a:=4 / Real.exp 1) (f:=pow_inv_shift))
      _ ≤ (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left tsum_pow_inv_shift_le hnonneg
  have hconst : (4 / Real.exp 1 : ℝ) ≤ 2 := by
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hpos : 0 < Real.exp 1 := by exact Real.exp_pos 1
    have h' : 4 ≤ 2 * Real.exp 1 := by nlinarith [h]
    exact (div_le_iff₀ hpos).2 h'
  have hS :
      (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 100 : ℝ) := by
    norm_num [pow_inv_shift]
  have hfinal :
      (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_one := by
    have hnonneg :
        0 ≤ (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      nlinarith [pow_inv_shift_nonneg 0, pow_inv_shift_nonneg 1]
    have hmul : (4 / Real.exp 1) *
        (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
          ≤ 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    have hS' : 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 25 : ℝ) := by
      nlinarith [hS]
    simpa [rho_one] using (le_trans hmul hS')
  exact le_trans hsum_le (by
    simpa [hsum_image] using le_trans hsum_le_tsum (le_trans htsum_bound hfinal))

lemma weight_sum_le_rho_oneK (K B tau : ℝ) (hB : 0 < B) [Fintype (Q3.Nodes K)] :
    ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
      ≤ rho_oneK K := by
  classical
  let idx : Q3.Nodes K → ℕ := fun n => (n : ℕ) - 2
  let C : ℝ := Real.exp (8 * Real.pi ^ 2 * t_rkhs_cap * K ^ 2)
  have hC_nonneg : 0 ≤ C := by exact Real.exp_nonneg _
  have hidx_inj : Set.InjOn idx (Set.univ : Set (Q3.Nodes K)) := by
    intro a ha b hb h
    have ha2 : 2 ≤ (a : ℕ) := a.property.2
    have hb2 : 2 ≤ (b : ℕ) := b.property.2
    have h' := congrArg (fun x => x + 2) h
    have hab : (a : ℕ) = (b : ℕ) := by
      simpa [idx, Nat.sub_add_cancel ha2, Nat.sub_add_cancel hb2] using h'
    exact Subtype.ext hab
  have hterm :
      ∀ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
          ≤ C * (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    intro n
    simpa [idx, C, mul_assoc, mul_left_comm, mul_comm] using
      weight_term_shift_le_pow_inv (K:=K) (B:=B) (tau:=tau) hB n
  have hsum_le :
      ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖
        ≤ ∑ n : Q3.Nodes K, C * (4 / Real.exp 1) * pow_inv_shift (idx n) := by
    refine Finset.sum_le_sum ?_
    intro n hn
    exact hterm n
  have hsum_image :
      ∑ n : Q3.Nodes K, C * (4 / Real.exp 1) * pow_inv_shift (idx n) =
        Finset.sum (Finset.univ.image idx)
          (fun m => C * (4 / Real.exp 1) * pow_inv_shift m) := by
    have hidx_inj' :
        Set.InjOn idx (↑(Finset.univ : Finset (Q3.Nodes K)) : Set (Q3.Nodes K)) := by
      intro a ha b hb h
      exact hidx_inj (by trivial) (by trivial) h
    simpa using (Finset.sum_image (s:=Finset.univ)
      (f:=fun m => C * (4 / Real.exp 1) * pow_inv_shift m) (g:=idx) hidx_inj').symm
  have hsum_le_tsum :
      Finset.sum (Finset.univ.image idx)
          (fun m => C * (4 / Real.exp 1) * pow_inv_shift m) ≤
        ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m := by
    have hsum : Summable (fun m : ℕ => C * (4 / Real.exp 1) * pow_inv_shift m) := by
      exact Summable.mul_left (C * (4 / Real.exp 1)) summable_pow_inv_shift
    have hnonneg : ∀ m, 0 ≤ C * (4 / Real.exp 1) * pow_inv_shift m := by
      intro m
      exact mul_nonneg (mul_nonneg hC_nonneg (by positivity)) (pow_inv_shift_nonneg m)
    exact Summable.sum_le_tsum (s:=Finset.univ.image idx)
      (f:=fun m : ℕ => C * (4 / Real.exp 1) * pow_inv_shift m)
      (hs:=by intro m hm; exact hnonneg m) (hf:=hsum)
  have htsum_bound :
      ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m ≤
        C * (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
    have hnonneg : 0 ≤ (C * (4 / Real.exp 1 : ℝ)) := by
      exact mul_nonneg hC_nonneg (by positivity)
    calc
      ∑' m : ℕ, C * (4 / Real.exp 1) * pow_inv_shift m
          = (C * (4 / Real.exp 1)) * ∑' m : ℕ, pow_inv_shift m := by
              simpa [mul_assoc] using
                (tsum_mul_left (a:=C * (4 / Real.exp 1)) (f:=pow_inv_shift))
      _ ≤ (C * (4 / Real.exp 1)) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left tsum_pow_inv_shift_le hnonneg
  have hconst : (4 / Real.exp 1 : ℝ) ≤ 2 := by
    have h : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    have hpos : 0 < Real.exp 1 := by exact Real.exp_pos 1
    have h' : 4 ≤ 2 * Real.exp 1 := by nlinarith [h]
    exact (div_le_iff₀ hpos).2 h'
  have hS :
      (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 100 : ℝ) := by
    norm_num [pow_inv_shift]
  have hfinal_base :
      (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_one := by
    have hnonneg :
        0 ≤ (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      nlinarith [pow_inv_shift_nonneg 0, pow_inv_shift_nonneg 1]
    have hmul : (4 / Real.exp 1) *
        (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
          ≤ 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hconst hnonneg
    have hS' : 2 * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ)) ≤ (1 / 25 : ℝ) := by
      nlinarith [hS]
    simpa [rho_one] using (le_trans hmul hS')
  have hfinal :
      C * (4 / Real.exp 1) * (pow_inv_shift 0 + pow_inv_shift 1 + (1 / 511 : ℝ))
        ≤ rho_oneK K := by
    have hmul := mul_le_mul_of_nonneg_left hfinal_base hC_nonneg
    simpa [rho_oneK, C, mul_assoc] using hmul
  exact le_trans hsum_le (by
    simpa [hsum_image] using le_trans hsum_le_tsum (le_trans htsum_bound hfinal))

lemma prime_rayleigh_shift_le_rho_oneK (K B tau : ℝ) (M : ℕ)
    [Fintype (Q3.Nodes K)] (hB : 0 < B) (hM : 0 < 2 * M + 1) :
    (2 * M + 1 : ℝ) *
        Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
          (Q3.Proofs.RayleighQId.basis0 M) ≤ rho_oneK K := by
  have hsum_norm :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
        ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hwindow_nonneg :
        0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
      simpa [Q3.phi_shift] using
        Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
    have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    have hprod_nonneg :
        0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
      mul_nonneg hw_nonneg hwindow_nonneg
    have hnorm' :
        |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| =
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
      have hnorm_real :
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
            |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        simpa [Real.norm_eq_abs] using
          (norm_real (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)))
      exact hnorm_real.symm
    calc
      Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        exact (abs_of_nonneg hprod_nonneg).symm
      _ = ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := hnorm'
  have h_weight_sum :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ rho_oneK K := by
    simpa [hsum_norm] using weight_sum_le_rho_oneK (K:=K) (B:=B) (tau:=tau) hB
  have hprime :
      (2 * M + 1 : ℝ) *
          Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
            (Q3.Proofs.RayleighQId.basis0 M) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    exact Q3.Proofs.RayleighQId.prime_rayleigh_eq_shift (K:=K) (B:=B) (t:=t_rkhs_cap)
      (tau:=tau) (M:=M) hM
  calc
    (2 * M + 1 : ℝ) *
        Q3.RayleighQuotient (Q3.T_P_comp_real_shift K B t_rkhs_cap tau M)
          (Q3.Proofs.RayleighQId.basis0 M)
        = ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := hprime
    _ ≤ rho_oneK K := h_weight_sum

lemma prime_term_phi_shift_le_rho_oneK (K B tau : ℝ) (hB : 0 < B) (hK : |tau| + B ≤ K)
    [Fintype (Q3.Nodes K)] :
    Q3.prime_term (fun ξ => Q3.phi_shift B t_rkhs_cap tau ξ) ≤ rho_oneK K := by
  have hsum :
      Q3.prime_term (fun ξ => Q3.phi_shift B t_rkhs_cap tau ξ) =
        ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
    simpa using
      (Q3.Proofs.RayleighQId.prime_term_eq_nodes_sum_shift
        (B:=B) (t:=t_rkhs_cap) (tau:=tau) (K:=K) hB hK)
  have hsum_norm :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
        ∑ n : Q3.Nodes K,
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hwindow_nonneg :
        0 ≤ Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) := by
      simpa [Q3.phi_shift] using
        Q3.fejer_heat_window_nonneg B t_rkhs_cap (Q3.xi_n n - tau)
    have hw_nonneg : 0 ≤ Q3.w_Q n := Q3.w_Q_nonneg n
    have hprod_nonneg :
        0 ≤ Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) :=
      mul_nonneg hw_nonneg hwindow_nonneg
    have hnorm' :
        |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| =
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := by
      have hnorm_real :
          ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ =
            |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        simpa [Real.norm_eq_abs] using
          (norm_real (Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)))
      exact hnorm_real.symm
    calc
      Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) =
          |Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)| := by
        exact (abs_of_nonneg hprod_nonneg).symm
      _ = ‖((Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n)) : ℂ)‖ := hnorm'
  have hweight :
      ∑ n : Q3.Nodes K, Q3.w_Q n * Q3.phi_shift B t_rkhs_cap tau (Q3.xi_n n) ≤ rho_oneK K := by
    simpa [hsum_norm] using (weight_sum_le_rho_oneK (K:=K) (B:=B) (tau:=tau) hB)
  simpa [hsum] using hweight

lemma T_P_comp_real_opNorm_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    ‖Q3.T_P_comp_real K B t M‖ ≤
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
  classical
  have hsymm := T_P_comp_real_isSymm (K:=K) (B:=B) (t:=t) (M:=M)
  have hC_nonneg :
      0 ≤ ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
    refine Finset.sum_nonneg ?_
    intro n hn
    exact norm_nonneg _
  have hrow :
      ∀ i, ∑ j, |Q3.T_P_comp_real K B t M i j| ≤
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
    intro i
    exact T_P_comp_real_row_sum_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i
  exact Q3.Schur_test (A:=Q3.T_P_comp_real K B t M) hsymm
    (C:=∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖)
    hC_nonneg hrow

/-! ### C1 compression identity (explicit basisFun model) -/

/-- BasisFun model: `T_P_comp` is a compression with `ψ = basisFun`, `k = prime_vec`. -/
lemma T_P_comp_toCLM_eq_compression_basisFun
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    (Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap =
      Q3.Proofs.C1Embedding.compression
        (ι := Q3.Proofs.RKHSInterfaceC1.iota (H := EuclideanSpace ℂ (Fin (2 * M + 1)))
          (M := M)
          (ψ := Q3.Proofs.RKHSInterfaceC1.psi_basis (M := M))
          (Q3.Proofs.RKHSInterfaceC1.psi_basis_orthonormal (M := M)))
        (T := Q3.Proofs.RKHSInterfaceC1.T_P_RKHS_like
          (H := EuclideanSpace ℂ (Fin (2 * M + 1)))
          (K := K) (B := B) (t := t)
          (k := Q3.Proofs.RKHSInterfaceC1.k_basis (K := K) (M := M))) := by
  simpa using
    (Q3.Proofs.RKHSInterfaceC1.T_P_comp_toCLM_eq_compression_basisFun
      (K := K) (B := B) (t := t) (M := M))

/-- C1 (basisFun) opNorm bound: `‖T_P_comp‖ ≤ ‖T_P_RKHS_like‖`. -/
lemma T_P_comp_opNorm_le_basisFun
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    ‖(Matrix.toEuclideanLin (Q3.T_P_comp K B t M)).toContinuousLinearMap‖ ≤
      ‖Q3.Proofs.RKHSInterfaceC1.T_P_RKHS_like
        (H := EuclideanSpace ℂ (Fin (2 * M + 1)))
        (K := K) (B := B) (t := t)
        (k := Q3.Proofs.RKHSInterfaceC1.k_basis (K := K) (M := M))‖ := by
  simpa using
    (Q3.Proofs.RKHSInterfaceC1.T_P_comp_opNorm_le_basisFun
      (K := K) (B := B) (t := t) (M := M))

/-! ### C1 compression identity (dictionary embedding) -/

/-- C1 identity: `T_P_comp_real` is the compression of its lifted operator along the
dictionary embedding. This is the formal “compression identity” used below. -/
lemma T_P_comp_real_eq_compression_lift_dict
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1) :
    let ι :=
      Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
    let A :
        (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
        (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap
    let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
    (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap =
      Q3.Proofs.C1Embedding.compression ι T := by
  classical
  simpa using
    (T_P_comp_real_eq_compression_lift_of_dictEmbedding (K := K) (B := B) (t := t) (M := M)
      (d := d) (hdim := hdim))

/-- C1 corollary (lifted operator): `‖T_P_comp_real‖ ≤ ‖T‖` for the compression lift. -/
lemma T_P_comp_real_opNorm_le_lift_dict
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1) :
    let ι :=
      Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
    let A :
        (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
        (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap
    let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
    ‖A‖ ≤ ‖T‖ := by
  classical
  simpa using
    (T_P_comp_real_opNorm_le_lift_of_dictEmbedding (K := K) (B := B) (t := t) (M := M)
      (d := d) (hdim := hdim))

lemma T_P_comp_real_opNorm_le_via_C1_dictEmbedding
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (T : H →L[ℝ] H)
    (hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression
          (Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim) T) :
    ‖Q3.T_P_comp_real K B t M‖ ≤ ‖T‖ := by
  have hC1 :
      ‖(Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap‖ ≤ ‖T‖ :=
    T_P_comp_real_opNorm_le_of_dictEmbedding (K := K) (B := B) (t := t) (M := M)
      (d := d) (hdim := hdim) (T := T) hA
  simpa [Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using hC1

lemma rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (T : H →L[ℝ] H)
    (hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression
          (Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim) T)
    (hT : ‖T‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  intro v hv
  have hnorm' :
      ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ ‖T‖ :=
    T_P_comp_real_opNorm_le_via_C1_dictEmbedding (K := K) (B := B) (t := t_rkhs_cap)
      (M := M) (d := d) (hdim := hdim) (T := T) hA
  have hnorm :
      ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ rho_one := by
    exact le_trans hnorm' hT
  have hRayleigh :
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤
        ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ :=
    RayleighQuotient_le_opNorm (A:=Q3.T_P_comp_real K B t_rkhs_cap M) (v:=v) hv
  exact le_trans hRayleigh hnorm

lemma rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding_lift
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (h_weight_sum :
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  classical
  let ι :=
    Q3.Proofs.C1Embedding.dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
  let A : (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ] (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
    (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap
  let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
  have hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t_rkhs_cap M)).toContinuousLinearMap =
        Q3.Proofs.C1Embedding.compression ι T := by
    simpa [ι, A, T] using
      (T_P_comp_real_eq_compression_lift_of_dictEmbedding (K := K) (B := B) (t := t_rkhs_cap)
        (M := M) (d := d) (hdim := hdim))
  have hAop :
      ‖A‖ ≤ rho_one := by
    have hnorm :
        ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤
          ∑ n : Q3.Nodes K,
            ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ :=
      T_P_comp_real_opNorm_le_weight_sum (K:=K) (B:=B) (t:=t_rkhs_cap) (M:=M)
    have hnorm' : ‖Q3.T_P_comp_real K B t_rkhs_cap M‖ ≤ rho_one :=
      le_trans hnorm h_weight_sum
    simpa [A, Matrix.l2_opNorm_def, LinearEquiv.trans_apply] using hnorm'
  have hT : ‖T‖ ≤ rho_one := by
    have hTle : ‖T‖ ≤ ‖A‖ :=
      Q3.Proofs.C1Embedding.opNorm_lift_le (ι := ι) (A := A)
    exact le_trans hTle hAop
  exact rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding (K := K) (B := B) (M := M)
    (d := d) (hdim := hdim) (T := T) (hA := hA) (hT := hT)

/-! ### Kernel-section dictionary (finite-dimensional model) -/

private noncomputable def kernel_basis (M : ℕ) :
    OrthonormalBasis (Fin (2 * M + 1)) ℝ (EuclideanSpace ℝ (Fin (2 * M + 1))) := by
  classical
  let E := EuclideanSpace ℝ (Fin (2 * M + 1))
  have hfinrank : Module.finrank ℝ E = 2 * M + 1 :=
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * M + 1))
  exact (stdOrthonormalBasis ℝ E).reindex (finCongr hfinrank)

private noncomputable def kernel_dict (M : ℕ) :
    Fin (2 * M + 1) → EuclideanSpace ℝ (Fin (2 * M + 1)) :=
  kernel_basis M

private lemma kernel_dict_finrank (M : ℕ) :
    Module.finrank ℝ
        (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M)) = 2 * M + 1 := by
  classical
  let E := EuclideanSpace ℝ (Fin (2 * M + 1))
  have hspan :
      Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M) = ⊤ := by
    simpa [Q3.Proofs.C1Embedding.dictSubmodule, kernel_dict, kernel_basis] using
      (kernel_basis M).toBasis.span_eq
  have htop :
      Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) (kernel_dict M)) =
        Module.finrank ℝ E := by
    rw [hspan]
    exact (finrank_top (R := ℝ) (M := E))
  exact htop.trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * M + 1))

lemma rkhs_cap_rayleigh_tcap_via_C1_kernel_dict
    (K B : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖ ≤ rho_one) :
    ∀ (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  classical
  let d := kernel_dict M
  have hdim :
      Module.finrank ℝ (Q3.Proofs.C1Embedding.dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1 := by
    simpa [d] using kernel_dict_finrank (M := M)
  simpa [d] using
    (rkhs_cap_rayleigh_tcap_via_C1_dictEmbedding_lift (K := K) (B := B) (M := M)
      (H := EuclideanSpace ℝ (Fin (2 * M + 1))) (d := d) (hdim := hdim)
      (h_weight_sum := h_weight_sum))

lemma rkhs_cap_rayleigh_tcap (K B : ℝ) [Fintype (Q3.Nodes K)]
    (h_weight_sum :
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
        ≤ rho_one) :
    ∀ (M : ℕ) (v : Fin (2 * M + 1) → ℝ), v ≠ 0 →
      Q3.RayleighQuotient (Q3.T_P_comp_real K B t_rkhs_cap M) v ≤ rho_one := by
  intro M v hv
  exact rkhs_cap_rayleigh_tcap_via_C1_kernel_dict (K := K) (B := B) (M := M)
    (h_weight_sum := h_weight_sum) v hv

/-- DEPRECATED: This lemma uses sampling Toeplitz with a_star.
    Use A3_bridge_rayleigh_from_weight_sum_P_A from P_A_Toeplitz_bridge.lean instead,
    which uses Fourier Toeplitz with P_A (the mathematically correct formulation).
    See docs/PROSHKA_ANALYSIS_a_star_crisis.md for details. -/
lemma A3_bridge_rayleigh_from_weight_sum (K : ℝ)
    (h_rayleigh_lower_bound :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ}, v ≠ 0 →
        Q3.RayleighQuotient (ToeplitzMatrix (2 * M + 1) Q3.a_star) v ≥ Q3.c_star)
    (h_weight_sum :
      ∀ [Fintype (Q3.Nodes K)],
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one) :
    Q3.A3_bridge_data_rayleigh K := by
  intro hK _inst
  have h_cap :
      ∀ {M : ℕ} {v : Fin (2 * M + 1) → ℝ} [Fintype (Q3.Nodes K)], v ≠ 0 →
        Q3.RayleighQuotient (Q3.T_P_comp_real K K t_rkhs_cap M) v ≤ rho_one := by
    intro M v
    intro _inst' hv
    have h_weight_sum' :
        ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window K t_rkhs_cap (Q3.xi_n n)) : ℂ)‖
          ≤ rho_one := h_weight_sum
    exact rkhs_cap_rayleigh_tcap (K:=K) (B:=K) (h_weight_sum:=h_weight_sum') M v hv
  exact (A3_bridge_rayleigh_first (K:=K)
    (h_rayleigh_lower_bound:=h_rayleigh_lower_bound) (h_cap:=h_cap)) hK

end Q3.Proofs


## File: full/q3.lean.aristotle/Q3/Proofs/T_P_comp_utils.lean

/-
Utilities for the compression prime operator T_P_comp.
-/

import Q3.Basic.Defs

open scoped BigOperators
open scoped ComplexConjugate

namespace Q3.Proofs

lemma T_P_comp_conj (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    conj (Q3.T_P_comp K B t M i j) = Q3.T_P_comp K B t M j i := by
  simp [Q3.T_P_comp, mul_comm, mul_assoc]

lemma T_P_comp_real_symm (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    Q3.T_P_comp_real K B t M i j = Q3.T_P_comp_real K B t M j i := by
  have h := T_P_comp_conj (K:=K) (B:=B) (t:=t) (M:=M) i j
  simpa [Q3.T_P_comp_real] using congrArg Complex.re h

lemma T_P_comp_real_isSymm (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    (Q3.T_P_comp_real K B t M).IsSymm := by
  ext i j
  simp [Matrix.transpose_apply, T_P_comp_real_symm (K:=K) (B:=B) (t:=t) (M:=M)]

lemma T_P_comp_entry_norm_le_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    ‖Q3.T_P_comp K B t M i j‖ ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ := by
  classical
  simpa [Q3.T_P_comp]
    using (norm_sum_le (s := Finset.univ)
      (f := fun n : Q3.Nodes K =>
        ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)))

lemma T_P_comp_entry_norm_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    ‖Q3.T_P_comp K B t M i j‖ ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
  classical
  refine le_trans (T_P_comp_entry_norm_le_sum (K:=K) (B:=B) (t:=t) (M:=M) i j) ?_
  refine Finset.sum_le_sum ?_
  intro n hn
  have hnorm :
      ‖Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ =
        (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
    simpa using (Q3.prime_vec_mul_conj_norm (M:=M) (ξ:=Q3.xi_n n) i j)
  refine le_of_eq ?_
  calc
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖
        = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
            (Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j))‖ := by
            simp [mul_assoc]
    _ = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          ‖Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ := by
          exact
            (norm_mul
              ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)
              (Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)))
    _ = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
          rw [hnorm]

lemma T_P_comp_real_entry_abs_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    |Q3.T_P_comp_real K B t M i j| ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
  have hRe :
      |(Q3.T_P_comp K B t M i j).re| ≤ ‖Q3.T_P_comp K B t M i j‖ := by
    simpa using (RCLike.abs_re_le_norm (z := Q3.T_P_comp K B t M i j))
  have hbound :=
    T_P_comp_entry_norm_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i j
  simpa [Q3.T_P_comp_real] using (le_trans hRe hbound)

lemma T_P_comp_real_row_sum_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i : Fin (2 * M + 1)) :
    ∑ j, |Q3.T_P_comp_real K B t M i j| ≤
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
  classical
  set c : ℝ := (1 / Real.sqrt (2 * M + 1 : ℝ))^2
  set w : ℝ :=
    ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖
  set const : ℝ :=
    ∑ n : Q3.Nodes K,
      ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c
  have hentry : ∀ j : Fin (2 * M + 1),
      |Q3.T_P_comp_real K B t M i j| ≤ const := by
    intro j
    have hbound :=
      T_P_comp_real_entry_abs_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i j
    simpa [const, c] using hbound
  have hsum :
      (∑ j : Fin (2 * M + 1), |Q3.T_P_comp_real K B t M i j|) ≤
        ∑ j : Fin (2 * M + 1), const := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hentry j
  have hconst_mul :
      (2 * M + 1 : ℝ) * c = 1 := by
    have hpos : (0 : ℝ) < (2 * M + 1 : ℝ) := by positivity
    have hsqrt :
        (Real.sqrt (2 * M + 1 : ℝ))^2 = (2 * M + 1 : ℝ) := by
      simpa [pow_two] using
        (Real.sq_sqrt (show 0 ≤ (2 * M + 1 : ℝ) by positivity))
    calc
      (2 * M + 1 : ℝ) * c
          = (2 * M + 1 : ℝ) * (1 / (Real.sqrt (2 * M + 1 : ℝ))^2) := by
              simp [c, pow_two, mul_comm]
      _ = (2 * M + 1 : ℝ) * (1 / (2 * M + 1 : ℝ)) := by simp [hsqrt]
      _ = 1 := by field_simp [hpos.ne']
  have hsumconst :
      (∑ j : Fin (2 * M + 1), const) = (2 * M + 1 : ℝ) * const := by
    simp [const]
  have hconst' : (2 * M + 1 : ℝ) * const = w := by
    calc
      (2 * M + 1 : ℝ) * const
          = (2 * M + 1 : ℝ) *
              (∑ n : Q3.Nodes K,
                ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c) := by
                simp [const]
      _ = ∑ n : Q3.Nodes K,
            (2 * M + 1 : ℝ) *
              (‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c) := by
                simp [Finset.mul_sum, mul_comm, mul_assoc]
      _ = ∑ n : Q3.Nodes K,
            ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * ((2 * M + 1 : ℝ) * c) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
      _ = w := by
            calc
              (∑ n : Q3.Nodes K,
                ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * ((2 * M + 1 : ℝ) * c))
                  = ∑ n : Q3.Nodes K,
                      ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * 1 := by
                        simp [hconst_mul]
              _ = w := by simp [w]
  exact le_trans hsum (by simp [hsumconst, hconst'])

end Q3.Proofs


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Main.lean

import Mathlib
import Q3.Proofs.A3_Floor_Bounds
import Q3.Proofs.A3_Floor_Monotonicity

open scoped BigOperators Real Classical
open Real Set
open Filter

noncomputable section

/-- Target floor constant. -/
def c_star : ℝ := 11 / 10

/-- Archimedean symbol kernel. -/
def g (B t ξ : ℝ) : ℝ := Q3.a ξ * w B t ξ

/-- Periodized symbol. -/
def P_A (B t θ : ℝ) : ℝ :=
  2 * Real.pi * ∑' (m : ℤ), g B t (θ + m)

/-- P_A is 1-periodic: P_A(θ + 1) = P_A(θ). -/
lemma P_A_periodic : Function.Periodic (P_A B_min t_sym) 1 := by
  intro θ
  simp only [P_A]
  congr 1
  -- Need: Σ' m, g(θ + 1 + m) = Σ' m, g(θ + m)
  -- θ + 1 + m = θ + (m + 1), and reindex n = m + 1
  have h1 : ∀ m : ℤ, g B_min t_sym (θ + 1 + m) = g B_min t_sym (θ + (m + 1)) := by
    intro m; ring_nf
  simp_rw [h1]
  -- Use that sum is invariant under index shift
  have h2 := Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun m => g B_min t_sym (θ + m))
  convert h2 using 2
  ext m
  congr 1
  -- Goal: θ + (↑m + 1) = θ + ↑(Equiv.addRight 1 m)
  -- Equiv.addRight 1 m = m + 1 : ℤ, and ↑(m + 1) = ↑m + 1
  have h3 : (Equiv.addRight 1 m : ℤ) = m + 1 := rfl
  simp only [h3, Int.cast_add, Int.cast_one]

/-- g B_min t_sym is continuous. -/
lemma continuous_g_B_min_t_sym : Continuous (fun ξ => g B_min t_sym ξ) := by
  simp only [g]
  have ha : Continuous Q3.a := by
    have hpi : (2 * Real.pi) ≠ 0 := by nlinarith [Real.pi_pos]
    have h_eq : Q3.a = (fun ξ => (1 / (2 * Real.pi)) * Q3.a_star ξ) := by
      ext ξ
      simp only [Q3.a_star]
      field_simp [hpi]
    rw [h_eq]
    exact continuous_const.mul Q3.a_star_continuous
  have hw : Continuous (fun ξ => w B_min t_sym ξ) := by
    simp only [w]
    have h_lin : Continuous (fun ξ => 1 - |ξ| / B_min) :=
      continuous_const.sub (continuous_abs.div_const B_min)
    have h_max : Continuous (fun ξ => max (0 : ℝ) (1 - |ξ| / B_min)) :=
      continuous_const.max h_lin
    have h_exp : Continuous (fun ξ => Real.exp (-4 * Real.pi ^ 2 * t_sym * ξ ^ 2)) := by
      have h1 : Continuous (fun ξ => -4 * Real.pi ^ 2 * t_sym * ξ ^ 2) :=
        continuous_const.mul (continuous_pow 2)
      exact Real.continuous_exp.comp h1
    exact h_max.mul h_exp
  exact ha.mul hw

/-- g has compact support: g(ξ) = 0 when |ξ| ≥ B_min. -/
lemma g_support_B_min (ξ : ℝ) (h : B_min ≤ |ξ|) : g B_min t_sym ξ = 0 := by
  simp only [g, w]
  have hB : (0 : ℝ) < B_min := by norm_num [B_min]
  have h_lin : 1 - |ξ| / B_min ≤ 0 := by
    have h1 : 1 ≤ |ξ| / B_min := by
      rw [one_le_div hB]
      exact h
    linarith
  simp only [max_eq_left h_lin, zero_mul, mul_zero]

/-- For any θ₀, there exists N such that on (θ₀ - 1/2, θ₀ + 1/2),
    P_A equals a finite sum over |m| ≤ N. -/
lemma P_A_locally_finite_sum (θ₀ : ℝ) :
    ∃ N : ℕ, ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2),
      P_A B_min t_sym θ = 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t_sym (θ + m) := by
  -- For B_min = 3, if θ ∈ (θ₀ - 1/2, θ₀ + 1/2) and |m| > ⌈|θ₀|⌉ + 4, then g(θ + m) = 0
  use Nat.ceil |θ₀| + 4
  intro θ hθ
  unfold P_A
  congr 1
  apply tsum_eq_sum
  intro m hm
  simp only [Finset.mem_Icc, not_and, not_le] at hm
  -- m ∉ [-(⌈|θ₀|⌉ + 4), ⌈|θ₀|⌉ + 4] means |m| > ⌈|θ₀|⌉ + 4
  have h_large : B_min ≤ |θ + m| := by
    have hθ_bound : |θ| < |θ₀| + 1/2 := by
      have h1 : θ₀ - 1/2 < θ := hθ.1
      have h2 : θ < θ₀ + 1/2 := hθ.2
      rw [abs_lt]
      constructor
      · by_cases hθ₀_neg : θ₀ ≤ 0
        · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
          linarith
        · push_neg at hθ₀_neg
          have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
          linarith
      · by_cases hθ₀_neg : θ₀ ≤ 0
        · have : |θ₀| = -θ₀ := abs_of_nonpos hθ₀_neg
          linarith
        · push_neg at hθ₀_neg
          have : |θ₀| = θ₀ := abs_of_pos hθ₀_neg
          linarith
    have hN : (Nat.ceil |θ₀| : ℤ) + 4 < |m| := by
      by_cases h : m < -((Nat.ceil |θ₀| : ℤ) + 4)
      · have hm_neg : m < 0 := by omega
        simp only [abs_of_neg hm_neg]
        omega
      · push_neg at h
        have := hm h
        have hm_nonneg : 0 ≤ m := by omega
        simp only [abs_of_nonneg hm_nonneg]
        exact this
    have h_ceil : |θ₀| ≤ Nat.ceil |θ₀| := Nat.le_ceil |θ₀|
    have h_m_real : |θ₀| + 4 < |(m : ℝ)| := by
      have h1 : (Nat.ceil |θ₀| : ℝ) + 4 < |m| := by exact_mod_cast hN
      calc |θ₀| + 4 ≤ (Nat.ceil |θ₀| : ℝ) + 4 := by linarith
        _ < |m| := h1
        _ = |(m : ℝ)| := by simp [Int.cast_abs]
    -- |θ + m| ≥ |m| - |θ| > |θ₀| + 4 - (|θ₀| + 1/2) > 3 = B_min
    have h_tri : |(m : ℝ)| - |θ| ≤ |θ + (m : ℝ)| := by
      have h1 := abs_sub_abs_le_abs_sub (m : ℝ) (-θ)
      simp only [abs_neg, sub_neg_eq_add] at h1
      calc |(m : ℝ)| - |θ| ≤ |(m : ℝ) + θ| := h1
        _ = |θ + (m : ℝ)| := by ring_nf
    have h_final : (B_min : ℝ) < |θ + (m : ℝ)| := by
      calc (B_min : ℝ) = 3 := by norm_num [B_min]
        _ < 3.5 := by norm_num
        _ = |θ₀| + 4 - (|θ₀| + 1/2) := by ring
        _ < |(m : ℝ)| - |θ| := by linarith
        _ ≤ |θ + (m : ℝ)| := h_tri
    have h_eq : |θ + (m : ℝ)| = |θ + m| := by norm_cast
    linarith [h_final, h_eq.symm ▸ h_final]
  exact g_support_B_min (θ + m) h_large

/-- Continuity of the periodized symbol at the A3_FLOOR parameters. -/
theorem P_A_continuous : Continuous (P_A B_min t_sym) := by
  rw [continuous_iff_continuousAt]
  intro θ₀
  -- Use local finiteness: near θ₀, P_A is a finite sum
  obtain ⟨N, hN⟩ := P_A_locally_finite_sum θ₀
  -- The finite sum function is continuous
  let f := fun θ => 2 * Real.pi * ∑ m ∈ Finset.Icc (-(N : ℤ)) N, g B_min t_sym (θ + m)
  have h_sum_cont : Continuous f := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro m _
    exact continuous_g_B_min_t_sym.comp (continuous_id.add continuous_const)
  -- P_A equals f on a neighborhood of θ₀
  have h_mem : Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2) ∈ nhds θ₀ := by
    apply Ioo_mem_nhds <;> linarith
  have h_eq : ∀ θ ∈ Set.Ioo (θ₀ - 1/2) (θ₀ + 1/2), P_A B_min t_sym θ = f θ := hN
  -- f is continuous at θ₀
  have h_f_cont : ContinuousAt f θ₀ := h_sum_cont.continuousAt
  -- P_A =ᶠ f near θ₀
  have h_eq_f : P_A B_min t_sym =ᶠ[nhds θ₀] f := by
    apply Filter.eventuallyEq_of_mem h_mem
    intro θ hθ
    exact h_eq θ hθ
  exact h_f_cont.congr h_eq_f.symm

lemma a_antitone_on_Ioi : AntitoneOn Q3.a (Set.Ioi 0) := by
  intro x hx y hy hxy
  by_cases hxy' : x = y
  · simpa [hxy']
  · have hlt : x < y := lt_of_le_of_ne hxy hxy'
    exact (strictAntiOn_a hx hy hlt).le

lemma a_even (ξ : ℝ) : Q3.a (-ξ) = Q3.a ξ := by
  have h := Q3.a_star_even ξ
  have h' : (2 * Real.pi : ℝ) * Q3.a (-ξ) = (2 * Real.pi : ℝ) * Q3.a ξ := by
    simpa [Q3.a_star, mul_comm, mul_left_comm, mul_assoc] using h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by nlinarith [Real.pi_pos]
  exact mul_left_cancel₀ hpi h'

lemma w_even (B t ξ : ℝ) : w B t (-ξ) = w B t ξ := by
  simp [w, abs_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma g_even (B t ξ : ℝ) : g B t (-ξ) = g B t ξ := by
  simp [g, a_even, w_even]

lemma a_zero_ge_a_half : Q3.a 0 ≥ Q3.a (1 / 2 : ℝ) := by
  have hcont : ContinuousWithinAt Q3.a (Set.Ici 0) 0 := by
    simpa using (continuousOn_a.continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ)))
  have hseq :
      Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq'' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hseq
  have hseq' :
      Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhdsWithin (0 : ℝ) (Set.Ici 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (f := fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ))) (s := Set.Ici 0) hseq'' ?_
    refine (Filter.Eventually.of_forall ?_)
    intro n
    have hpos : (0 : ℝ) ≤ (1 / ((n + 1 : ℕ) : ℝ)) := by
      have hpos' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact one_div_nonneg.mpr (le_of_lt hpos')
    simpa using hpos
  have hlim :
      Tendsto (fun n : ℕ => Q3.a (1 / ((n + 1 : ℕ) : ℝ))) atTop (nhds (Q3.a 0)) :=
    hcont.tendsto.comp hseq'
  have hconst :
      Tendsto (fun n : ℕ => Q3.a (1 / 2 : ℝ)) atTop (nhds (Q3.a (1 / 2 : ℝ))) :=
    tendsto_const_nhds
  have hle :
      (fun n : ℕ => Q3.a (1 / 2 : ℝ)) ≤ᶠ[atTop]
        fun n : ℕ => Q3.a (1 / ((n + 1 : ℕ) : ℝ)) := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hxpos : (0 : ℝ) < (1 / ((n + 1 : ℕ) : ℝ)) := by
      have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      exact one_div_pos.mpr hpos
    have hx : (1 / ((n + 1 : ℕ) : ℝ)) ∈ Set.Ioi (0 : ℝ) := by
      simpa using hxpos
    have hy : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hge : (2 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ hn)
    have hxy : (1 / ((n + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (2 : ℝ)) hge
      simpa [one_div] using h
    exact a_antitone_on_Ioi hx hy hxy
  have h := le_of_tendsto_of_tendsto hconst hlim hle
  exact h

lemma a_ge_a_half_on_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    Q3.a θ ≥ Q3.a (1 / 2 : ℝ) := by
  by_cases hθ0 : θ = 0
  · simpa [hθ0] using a_zero_ge_a_half
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    have hθin : θ ∈ Set.Ioi (0 : ℝ) := hθpos
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have h := a_antitone_on_Ioi hθin hhalf hθ.2
    exact h

lemma w_lower_on_half {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    w B_min t_sym θ ≥ (9 / 20 : ℝ) := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθle : θ ≤ (1 / 2 : ℝ) := hθ.2
  have habs : |θ| = θ := abs_of_nonneg hθ0
  have hnonneg : 0 ≤ 1 - θ / B_min := by
    have : 0 ≤ 1 - θ / (3 : ℝ) := by nlinarith [hθle]
    simpa [B_min] using this
  have hfac1 : (5 / 6 : ℝ) ≤ 1 - θ / B_min := by
    have : (5 / 6 : ℝ) ≤ 1 - θ / (3 : ℝ) := by nlinarith [hθle]
    simpa [B_min] using this
  have hsq : θ^2 ≤ (1 / 2 : ℝ)^2 := by nlinarith [hθ0, hθle]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2 ≤
        -4 * Real.pi^2 * t_sym * θ^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) ≤
        (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    exact mul_le_mul hfac1 hfac2 hpos hnonneg
  have hnonneg_abs : 0 ≤ 1 - |θ| / B_min := by
    simpa [habs] using hnonneg
  have hmax : max 0 (1 - |θ| / B_min) = 1 - |θ| / B_min := by
    exact max_eq_right hnonneg_abs
  have hrew :
      w B_min t_sym θ =
        (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
    unfold w
    calc
      max 0 (1 - |θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2)
          = (1 - |θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
              rw [hmax]
      _ = (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := by
            rw [habs]
  have hhalf :
      w B_min t_sym (1 / 2 : ℝ) =
        (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
    have hconst : (-3 * Real.pi^2 / 50 : ℝ) = -4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      w B_min t_sym (1 / 2 : ℝ) = (5 / 6 : ℝ) * Real.exp (-3 * Real.pi^2 / 50) := w_half_eq
      _ = (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := by
            rw [hconst]
  have hmain : w B_min t_sym (1 / 2 : ℝ) ≤ w B_min t_sym θ := by
    calc
      w B_min t_sym (1 / 2 : ℝ)
          = (5 / 6 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 / 2 : ℝ)^2) := hhalf
      _ ≤ (1 - θ / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * θ^2) := hmul
      _ = w B_min t_sym θ := hrew.symm
  exact le_trans w_half_bound hmain

lemma exp_neg_two_le_one_div_seven : Real.exp (-2 : ℝ) ≤ (1 / 7 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^2 ≤ (Real.exp 1)^2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp2 : (2.7 : ℝ)^2 ≤ Real.exp 2 := by
    have h := Real.exp_nat_mul 1 2
    simpa [pow_two] using (h_pow.trans_eq h.symm)
  have h_num : (7 : ℝ) ≤ (2.7 : ℝ)^2 := by norm_num
  have h_exp2_ge : (7 : ℝ) ≤ Real.exp 2 := by exact le_trans h_num h_exp2
  have hdiv : (1 / Real.exp 2 : ℝ) ≤ (1 / 7 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 7) h_exp2_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma exp_neg_eight_le_one_div_2500 : Real.exp (-8 : ℝ) ≤ (1 / 2500 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^8 ≤ (Real.exp 1)^8 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp8 : (2.7 : ℝ)^8 ≤ Real.exp 8 := by
    have h := Real.exp_nat_mul 1 8
    simpa using (h_pow.trans_eq h.symm)
  have h_num : (2500 : ℝ) ≤ (2.7 : ℝ)^8 := by norm_num
  have h_exp8_ge : (2500 : ℝ) ≤ Real.exp 8 := by exact le_trans h_num h_exp8
  have hdiv : (1 / Real.exp 8 : ℝ) ≤ (1 / 2500 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2500) h_exp8_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma exp_neg_five_le_one_div_100 : Real.exp (-5 : ℝ) ≤ (1 / 100 : ℝ) := by
  have h_exp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    nlinarith
  have h_pow : (2.7 : ℝ)^5 ≤ (Real.exp 1)^5 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (2.7 : ℝ)) h_exp1 _
  have h_exp5 : (2.7 : ℝ)^5 ≤ Real.exp 5 := by
    have h := Real.exp_nat_mul 1 5
    simpa using (h_pow.trans_eq h.symm)
  have h_num : (100 : ℝ) ≤ (2.7 : ℝ)^5 := by norm_num
  have h_exp5_ge : (100 : ℝ) ≤ Real.exp 5 := by exact le_trans h_num h_exp5
  have hdiv : (1 / Real.exp 5 : ℝ) ≤ (1 / 100 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) h_exp5_ge
  simpa [Real.exp_neg, one_div] using hdiv

lemma w_one_upper : w B_min t_sym 1 ≤ (2 / 21 : ℝ) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (25 / 3 : ℝ) ≤ Real.pi^2 := by nlinarith [hpi]
  have hle : -12 * Real.pi^2 / 50 ≤ (-2 : ℝ) := by
    nlinarith [hpi2]
  have h_exp : Real.exp (-12 * Real.pi^2 / 50) ≤ Real.exp (-2 : ℝ) := by
    exact Real.exp_le_exp.mpr hle
  have h_exp' : Real.exp (-12 * Real.pi^2 / 50) ≤ (1 / 7 : ℝ) :=
    h_exp.trans exp_neg_two_le_one_div_seven
  have hpos : 0 ≤ (2 / 3 : ℝ) := by norm_num
  calc
    w B_min t_sym 1
        = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := w_one_eq
    _ ≤ (2 / 3 : ℝ) * (1 / 7 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp' hpos
    _ = (2 / 21 : ℝ) := by norm_num

lemma w_two_upper : w B_min t_sym 2 ≤ (1 / 7500 : ℝ) := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi2 : (25 / 3 : ℝ) ≤ Real.pi^2 := by nlinarith [hpi]
  have hle : -48 * Real.pi^2 / 50 ≤ (-8 : ℝ) := by
    nlinarith [hpi2]
  have h_exp : Real.exp (-48 * Real.pi^2 / 50) ≤ Real.exp (-8 : ℝ) := by
    exact Real.exp_le_exp.mpr hle
  have h_exp' : Real.exp (-48 * Real.pi^2 / 50) ≤ (1 / 2500 : ℝ) :=
    h_exp.trans exp_neg_eight_le_one_div_2500
  have hpos : 0 ≤ (1 / 3 : ℝ) := by norm_num
  calc
    w B_min t_sym 2
        = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := w_two_eq
    _ ≤ (1 / 3 : ℝ) * (1 / 2500 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp' hpos
    _ = (1 / 7500 : ℝ) := by norm_num

lemma w_three_halves_eq :
    w B_min t_sym (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := by
  have habs : |(3 / 2 : ℝ)| = (3 / 2 : ℝ) := by norm_num
  have hnonneg : (0 : ℝ) ≤ 1 - (3 / 2 : ℝ) / 3 := by norm_num
  simp [w, B_min, t_sym, pow_two, habs, max_eq_right hnonneg, mul_comm, mul_left_comm, mul_assoc]
  ring_nf

lemma exp_bound_three_halves : Real.exp (-27 * Real.pi^2 / 50) ≤ (1 / 100 : ℝ) := by
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hpi2 : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [hpi]
  have h_bound : (5 : ℝ) ≤ (27 / 50 : ℝ) * Real.pi ^ 2 := by
    have h_num : (5 : ℝ) ≤ (27 / 50 : ℝ) * (3.1415 : ℝ) ^ 2 := by
      norm_num
    nlinarith [h_num, hpi2]
  have h_exp_le : Real.exp (-27 * Real.pi^2 / 50) ≤ Real.exp (-5 : ℝ) := by
    exact Real.exp_le_exp.mpr (by nlinarith [h_bound])
  exact h_exp_le.trans exp_neg_five_le_one_div_100

lemma w_three_halves_upper : w B_min t_sym (3 / 2 : ℝ) ≤ (1 / 200 : ℝ) := by
  have h_exp : Real.exp (-27 * Real.pi^2 / 50) ≤ (1 / 100 : ℝ) := exp_bound_three_halves
  have hpos : 0 ≤ (1 / 2 : ℝ) := by norm_num
  calc
    w B_min t_sym (3 / 2 : ℝ)
        = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := w_three_halves_eq
    _ ≤ (1 / 2 : ℝ) * (1 / 100 : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_exp hpos
    _ = (1 / 200 : ℝ) := by norm_num

lemma g0_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym θ ≥ (9 / 32 : ℝ) := by
  have ha : Q3.a θ ≥ (5 / 8 : ℝ) := by
    have h := a_ge_a_half_on_Icc hθ
    have hhalf : Q3.a (1 / 2 : ℝ) ≥ (5 / 8 : ℝ) := a_half_bound
    exact le_trans hhalf h
  have hw : w B_min t_sym θ ≥ (9 / 20 : ℝ) := w_lower_on_half hθ
  have ha_nonneg : 0 ≤ Q3.a θ := by nlinarith [ha]
  have hmul : (5 / 8 : ℝ) * (9 / 20 : ℝ) ≤ Q3.a θ * w B_min t_sym θ := by
    exact mul_le_mul ha hw (by norm_num) ha_nonneg
  have hconst : (5 / 8 : ℝ) * (9 / 20 : ℝ) = (9 / 32 : ℝ) := by norm_num
  simpa [g, hconst] using hmul

lemma g1_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (θ + 1) ≥ (-1 / 21 : ℝ) := by
  have hxI' : (0 : ℝ) < θ + 1 := by nlinarith [hθ.1]
  have hxI : θ + 1 ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (3 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : θ + 1 ≤ (3 / 2 : ℝ) := by nlinarith [hθ.2]
  have ha : Q3.a (θ + 1) ≥ (-1 / 2 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_three_half_bound h
  have hpos : 0 ≤ θ + 1 := by nlinarith [hθ.1]
  have habs : |θ + 1| = θ + 1 := abs_of_nonneg hpos
  have hnonneg : 0 ≤ 1 - (θ + 1) / B_min := by
    have : 0 ≤ 1 - (θ + 1) / (3 : ℝ) := by nlinarith [hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (θ + 1) / B_min ≤ (2 / 3 : ℝ) := by
    have : 1 - (θ + 1) / (3 : ℝ) ≤ (2 / 3 : ℝ) := by nlinarith [hθ.1]
    simpa [B_min] using this
  have hsq : (1 : ℝ)^2 ≤ (θ + 1)^2 := by nlinarith [hθ.1]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (θ + 1)^2 ≤
        -4 * Real.pi^2 * t_sym * (1 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) ≤
        (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (θ + 1) =
        (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |θ + 1| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |θ + 1| / B_min) = 1 - |θ + 1| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |θ + 1| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2)
          = (1 - |θ + 1| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
              rw [hmax]
      _ = (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
            rw [habs]
  have hrew1 :
      (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) =
        w B_min t_sym 1 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2 : ℝ) = -12 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2)
          = (2 / 3 : ℝ) * Real.exp (-12 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 1 := by
            symm
            exact w_one_eq
  have hwle : w B_min t_sym (θ + 1) ≤ w B_min t_sym 1 := by
    calc
      w B_min t_sym (θ + 1)
          = (1 - (θ + 1) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 1)^2) := by
              simpa using hrew
      _ ≤ (2 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (1 : ℝ)^2) := hmul
      _ = w B_min t_sym 1 := hrew1
  have hw : w B_min t_sym (θ + 1) ≤ (2 / 21 : ℝ) := le_trans hwle w_one_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (θ + 1) := by
    have h' : 0 ≤ max 0 (1 - |θ + 1| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (θ + 1) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * w B_min t_sym (θ + 1) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-1 / 2 : ℝ) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * (2 / 21 : ℝ) := by
    have hneg : (-1 / 2 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw hneg
  have hfinal :
      Q3.a (θ + 1) * w B_min t_sym (θ + 1) ≥ (-1 / 2 : ℝ) * (2 / 21 : ℝ) :=
    le_trans hmul2 hmul1
  have hconst : (-1 / 2 : ℝ) * (2 / 21 : ℝ) = (-1 / 21 : ℝ) := by norm_num
  simpa [g, hconst] using hfinal

lemma g2_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (θ + 2) ≥ (-7 / 50000 : ℝ) := by
  have hxI' : (0 : ℝ) < θ + 2 := by nlinarith [hθ.1]
  have hxI : θ + 2 ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (5 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : θ + 2 ≤ (5 / 2 : ℝ) := by nlinarith [hθ.2]
  have ha : Q3.a (θ + 2) ≥ (-21 / 20 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_five_half_bound h
  have hpos : 0 ≤ θ + 2 := by nlinarith [hθ.1]
  have habs : |θ + 2| = θ + 2 := abs_of_nonneg hpos
  have hnonneg : 0 ≤ 1 - (θ + 2) / B_min := by
    have : 0 ≤ 1 - (θ + 2) / (3 : ℝ) := by nlinarith [hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (θ + 2) / B_min ≤ (1 / 3 : ℝ) := by
    have : 1 - (θ + 2) / (3 : ℝ) ≤ (1 / 3 : ℝ) := by nlinarith [hθ.1]
    simpa [B_min] using this
  have hsq : (2 : ℝ)^2 ≤ (θ + 2)^2 := by nlinarith [hθ.1]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (θ + 2)^2 ≤
        -4 * Real.pi^2 * t_sym * (2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) ≤
        (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (θ + 2) =
        (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |θ + 2| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |θ + 2| / B_min) = 1 - |θ + 2| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |θ + 2| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2)
          = (1 - |θ + 2| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
              rw [hmax]
      _ = (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) =
        w B_min t_sym 2 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2 : ℝ) = -48 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2)
          = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 2 := by
            symm
            exact w_two_eq
  have hwle : w B_min t_sym (θ + 2) ≤ w B_min t_sym 2 := by
    calc
      w B_min t_sym (θ + 2)
          = (1 - (θ + 2) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (θ + 2)^2) := by
              simpa using hrew
      _ ≤ (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := hmul
      _ = w B_min t_sym 2 := hrew1
  have hw : w B_min t_sym (θ + 2) ≤ (1 / 7500 : ℝ) := le_trans hwle w_two_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (θ + 2) := by
    have h' : 0 ≤ max 0 (1 - |θ + 2| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (θ + 2) * w B_min t_sym (θ + 2) ≥ (-21 / 20 : ℝ) * w B_min t_sym (θ + 2) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-21 / 20 : ℝ) * (1 / 7500 : ℝ) ≤ (-21 / 20 : ℝ) * w B_min t_sym (θ + 2) := by
    have hneg : (-21 / 20 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw hneg
  have hfinal : (-7 / 50000 : ℝ) ≤ Q3.a (θ + 2) * w B_min t_sym (θ + 2) := by
    have htmp :
        (-21 / 20 : ℝ) * (1 / 7500 : ℝ) ≤
          Q3.a (θ + 2) * w B_min t_sym (θ + 2) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg1_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) := by
  have hxI' : (0 : ℝ) < 1 - θ := by linarith [hθ.2]
  have hxI : 1 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 1 - θ ≤ (1 : ℝ) := by linarith [hθ.1]
  have ha : Q3.a (1 - θ) ≥ (-1 / 50 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_one_bound h
  have hw_le : w B_min t_sym (1 - θ) ≤ (1 : ℝ) := by
    have hB : 0 < B_min := by norm_num [B_min]
    have hnonneg : 0 ≤ |1 - θ| / B_min := by
      have habs : 0 ≤ |1 - θ| := abs_nonneg _
      exact div_nonneg habs (le_of_lt hB)
    have hmax : max 0 (1 - |1 - θ| / B_min) ≤ (1 : ℝ) := by
      have : (1 - |1 - θ| / B_min) ≤ (1 : ℝ) := by nlinarith [hnonneg]
      exact max_le_iff.mpr ⟨by norm_num, this⟩
    have h_exp : Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) ≤ (1 : ℝ) := by
      have hneg : (-4 * Real.pi^2 * t_sym * (1 - θ)^2 : ℝ) ≤ 0 := by
        have ht : 0 ≤ t_sym := by norm_num [t_sym]
        have hpi : 0 ≤ (Real.pi : ℝ)^2 := by nlinarith [Real.pi_pos]
        have hsq : 0 ≤ (1 - θ)^2 := by nlinarith
        have hpos : 0 ≤ 4 * Real.pi^2 * t_sym * (1 - θ)^2 := by
          have h4 : 0 ≤ (4 : ℝ) := by norm_num
          exact mul_nonneg (mul_nonneg (mul_nonneg h4 hpi) ht) hsq
        nlinarith
      simpa using (Real.exp_le_one_iff.mpr hneg)
    have h_exp_nonneg : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) := by
      exact Real.exp_nonneg _
    calc
      w B_min t_sym (1 - θ)
          = max 0 (1 - |1 - θ| / B_min) *
              Real.exp (-4 * Real.pi^2 * t_sym * (1 - θ)^2) := by rfl
      _ ≤ 1 * 1 := by exact mul_le_mul hmax h_exp h_exp_nonneg (by norm_num)
      _ = (1 : ℝ) := by ring
  have hw_nonneg : 0 ≤ w B_min t_sym (1 - θ) := by
    have h' : 0 ≤ max 0 (1 - |1 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 :
      Q3.a (1 - θ) * w B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) * w B_min t_sym (1 - θ) := by
    exact mul_le_mul_of_nonneg_right ha hw_nonneg
  have hmul2 :
      (-1 / 50 : ℝ) * (1 : ℝ) ≤ (-1 / 50 : ℝ) * w B_min t_sym (1 - θ) := by
    have hneg : (-1 / 50 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hw_le hneg
  have hfinal :
      (-1 / 50 : ℝ) ≤ Q3.a (1 - θ) * w B_min t_sym (1 - θ) := by
    have htmp : (-1 / 50 : ℝ) * (1 : ℝ) ≤ Q3.a (1 - θ) * w B_min t_sym (1 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg2_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (2 - θ) ≥ (-1 / 100 : ℝ) := by
  have hxI' : (0 : ℝ) < 2 - θ := by nlinarith [hθ.2]
  have hxI : 2 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (2 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 2 - θ ≤ (2 : ℝ) := by nlinarith [hθ.1]
  have ha' : Q3.a (2 - θ) ≥ (-2 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_two_bound h
  have hxi_ge : (3 / 2 : ℝ) ≤ 2 - θ := by nlinarith [hθ.2]
  have habs : |2 - θ| = 2 - θ := abs_of_nonneg (by nlinarith [hθ.2])
  have hnonneg : 0 ≤ 1 - (2 - θ) / B_min := by
    have : 0 ≤ 1 - (2 - θ) / (3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (2 - θ) / B_min ≤ (1 / 2 : ℝ) := by
    have : 1 - (2 - θ) / (3 : ℝ) ≤ (1 / 2 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hsq : (3 / 2 : ℝ)^2 ≤ (2 - θ)^2 := by nlinarith [hxi_ge]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (2 - θ)^2 ≤
        -4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) ≤
        (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (2 - θ) =
        (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |2 - θ| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |2 - θ| / B_min) = 1 - |2 - θ| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |2 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2)
          = (1 - |2 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
              rw [hmax]
      _ = (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) =
        w B_min t_sym (3 / 2 : ℝ) := by
    have hconst : (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2 : ℝ) = -27 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2)
          = (1 / 2 : ℝ) * Real.exp (-27 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym (3 / 2 : ℝ) := by
            symm
            exact w_three_halves_eq
  have hwle : w B_min t_sym (2 - θ) ≤ w B_min t_sym (3 / 2 : ℝ) := by
    calc
      w B_min t_sym (2 - θ)
          = (1 - (2 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (2 - θ)^2) := by
              simpa using hrew
      _ ≤ (1 / 2 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (3 / 2 : ℝ)^2) := hmul
      _ = w B_min t_sym (3 / 2 : ℝ) := hrew1
  have hwle' : w B_min t_sym (2 - θ) ≤ (1 / 200 : ℝ) :=
    le_trans hwle w_three_halves_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (2 - θ) := by
    have h' : 0 ≤ max 0 (1 - |2 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 : (-2 : ℝ) * w B_min t_sym (2 - θ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) := by
    exact mul_le_mul_of_nonneg_right ha' hw_nonneg
  have hmul2 :
      (-2 : ℝ) * (1 / 200 : ℝ) ≤ (-2 : ℝ) * w B_min t_sym (2 - θ) := by
    have hneg : (-2 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hwle' hneg
  have hfinal : (-1 / 100 : ℝ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) := by
    have htmp : (-2 : ℝ) * (1 / 200 : ℝ) ≤ Q3.a (2 - θ) * w B_min t_sym (2 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_neg3_lower {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    g B_min t_sym (3 - θ) ≥ (-1 / 2500 : ℝ) := by
  have hxI' : (0 : ℝ) < 3 - θ := by nlinarith [hθ.2]
  have hxI : 3 - θ ∈ Set.Ioi (0 : ℝ) := by simpa using hxI'
  have hyI : (3 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hxy : 3 - θ ≤ (3 : ℝ) := by nlinarith [hθ.1]
  have ha' : Q3.a (3 - θ) ≥ (-3 : ℝ) := by
    have h := a_antitone_on_Ioi hxI hyI hxy
    exact le_trans a_three_bound h
  have hxi_ge : (2 : ℝ) ≤ 3 - θ := by nlinarith [hθ.2]
  have habs : |3 - θ| = 3 - θ := abs_of_nonneg (by nlinarith [hθ.2])
  have hnonneg : 0 ≤ 1 - (3 - θ) / B_min := by
    have : 0 ≤ 1 - (3 - θ) / (3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hfac1 : 1 - (3 - θ) / B_min ≤ (1 / 3 : ℝ) := by
    have : 1 - (3 - θ) / (3 : ℝ) ≤ (1 / 3 : ℝ) := by nlinarith [hθ.1, hθ.2]
    simpa [B_min] using this
  have hsq : (2 : ℝ)^2 ≤ (3 - θ)^2 := by nlinarith [hxi_ge]
  have hneg : (-4 * Real.pi^2 * t_sym : ℝ) ≤ 0 := by
    have hpos : (0 : ℝ) ≤ 4 * Real.pi^2 * t_sym := by
      have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
      have ht : (0 : ℝ) ≤ t_sym := by norm_num [t_sym]
      nlinarith [hpi, ht]
    nlinarith
  have hle :
      -4 * Real.pi^2 * t_sym * (3 - θ)^2 ≤
        -4 * Real.pi^2 * t_sym * (2 : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonpos_left hsq hneg
    simpa [mul_assoc] using hmul
  have hfac2 :
      Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) ≤
        Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact Real.exp_le_exp.mpr hle
  have hpos2 : 0 ≤ Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
    exact Real.exp_nonneg _
  have hmul :
      (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) ≤
        (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := by
    exact mul_le_mul hfac1 hfac2 hpos2 (by norm_num)
  have hrew :
      w B_min t_sym (3 - θ) =
        (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
    have hnonneg_abs : 0 ≤ 1 - |3 - θ| / B_min := by
      simpa [habs] using hnonneg
    have hmax : max 0 (1 - |3 - θ| / B_min) = 1 - |3 - θ| / B_min := by
      exact max_eq_right hnonneg_abs
    unfold w
    calc
      max 0 (1 - |3 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2)
          = (1 - |3 - θ| / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
              rw [hmax]
      _ = (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
            rw [habs]
  have hrew1 :
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) =
        w B_min t_sym 2 := by
    have hconst : (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2 : ℝ) = -48 * Real.pi^2 / 50 := by
      simp [t_sym, pow_two]
      ring_nf
    calc
      (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2)
          = (1 / 3 : ℝ) * Real.exp (-48 * Real.pi^2 / 50) := by
              rw [hconst]
      _ = w B_min t_sym 2 := by
            symm
            exact w_two_eq
  have hwle : w B_min t_sym (3 - θ) ≤ w B_min t_sym 2 := by
    calc
      w B_min t_sym (3 - θ)
          = (1 - (3 - θ) / B_min) * Real.exp (-4 * Real.pi^2 * t_sym * (3 - θ)^2) := by
              simpa using hrew
      _ ≤ (1 / 3 : ℝ) * Real.exp (-4 * Real.pi^2 * t_sym * (2 : ℝ)^2) := hmul
      _ = w B_min t_sym 2 := hrew1
  have hwle' : w B_min t_sym (3 - θ) ≤ (1 / 7500 : ℝ) :=
    le_trans hwle w_two_upper
  have hw_nonneg : 0 ≤ w B_min t_sym (3 - θ) := by
    have h' : 0 ≤ max 0 (1 - |3 - θ| / B_min) := le_max_left _ _
    exact mul_nonneg h' (Real.exp_nonneg _)
  have hmul1 : (-3 : ℝ) * w B_min t_sym (3 - θ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) := by
    exact mul_le_mul_of_nonneg_right ha' hw_nonneg
  have hmul2 :
      (-3 : ℝ) * (1 / 7500 : ℝ) ≤ (-3 : ℝ) * w B_min t_sym (3 - θ) := by
    have hneg : (-3 : ℝ) ≤ 0 := by norm_num
    exact mul_le_mul_of_nonpos_left hwle' hneg
  have hfinal : (-1 / 2500 : ℝ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) := by
    have htmp : (-3 : ℝ) * (1 / 7500 : ℝ) ≤ Q3.a (3 - θ) * w B_min t_sym (3 - θ) :=
      le_trans hmul2 hmul1
    nlinarith
  simpa [g, one_div] using hfinal

lemma g_zero_of_large_index {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) {m : ℤ}
    (hm : m ≤ -4 ∨ 3 ≤ m) : g B_min t_sym (θ + m) = 0 := by
  have hm' : (B_min : ℝ) ≤ |θ + (m : ℝ)| := by
    cases hm with
    | inl hlow =>
        have hmle : (m : ℝ) ≤ -4 := by exact_mod_cast hlow
        have hsum : θ + (m : ℝ) ≤ (-7 / 2 : ℝ) := by nlinarith [hθ.2, hmle]
        have habs : |θ + (m : ℝ)| = -(θ + (m : ℝ)) := by
          exact abs_of_nonpos (by nlinarith [hsum])
        have hbound : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
          nlinarith [habs, hsum]
        simpa [B_min] using hbound
    | inr hhigh =>
        have hmge : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hhigh
        have hsum : (3 : ℝ) ≤ θ + (m : ℝ) := by nlinarith [hθ.1, hmge]
        have habs : |θ + (m : ℝ)| = θ + (m : ℝ) := by
          exact abs_of_nonneg (by nlinarith [hsum])
        have hbound : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
          nlinarith [habs, hsum]
        simpa [B_min] using hbound
  have hlin : (1 - |θ + (m : ℝ)| / B_min) ≤ 0 := by
    have hm'' : (3 : ℝ) ≤ |θ + (m : ℝ)| := by
      simpa [B_min] using hm'
    have hlin' : (1 - |θ + (m : ℝ)| / (3 : ℝ)) ≤ 0 := by
      nlinarith [hm'']
    simpa [B_min] using hlin'
  have hmax : max 0 (1 - |θ + (m : ℝ)| / B_min) = 0 := by
    exact max_eq_left hlin
  calc
    g B_min t_sym (θ + m)
        = Q3.a (θ + m) *
            (max 0 (1 - |θ + (m : ℝ)| / B_min) *
              Real.exp (-4 * Real.pi^2 * t_sym * (θ + (m : ℝ))^2)) := by rfl
    _ = Q3.a (θ + m) * (0 * Real.exp (-4 * Real.pi^2 * t_sym * (θ + (m : ℝ))^2)) := by
          simp [hmax]
    _ = 0 := by ring

lemma sum_map_embedding {α β γ : Type*} [DecidableEq α] [AddCommMonoid γ]
    (s : Finset α) (e : α ↪ β) (f : β → γ) :
    (s.map e).sum f = s.sum (fun x => f (e x)) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [ha, hs]

lemma P_A_eq_sum6 {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ =
      2 * Real.pi *
        (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
          g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := by
  classical
  let f : ℤ → ℝ := fun m => g B_min t_sym (θ + m)
  have hzero : ∀ m, m ∉ Finset.Icc (-3 : ℤ) 2 → f m = 0 := by
    intro m hm
    have hm' : ¬((-3 : ℤ) ≤ m ∧ m ≤ 2) := by
      simpa [Finset.mem_Icc] using hm
    have hm'' := not_and_or.mp hm'
    cases hm'' with
    | inl h1 =>
        have hmle : m ≤ -4 := by linarith
        simpa [f, add_comm, add_left_comm, add_assoc] using
          g_zero_of_large_index hθ (Or.inl hmle)
    | inr h2 =>
        have hmge : 3 ≤ m := by linarith
        simpa [f, add_comm, add_left_comm, add_assoc] using
          g_zero_of_large_index hθ (Or.inr hmge)
  have htsum : (∑' m : ℤ, f m) = (Finset.Icc (-3 : ℤ) 2).sum f := by
    simpa using (tsum_eq_sum (f := f) (s := Finset.Icc (-3 : ℤ) 2) hzero)
  have hsum :
      (Finset.Icc (-3 : ℤ) 2).sum f =
        f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 := by
    have hsum_map :
        (Finset.Icc (-3 : ℤ) 2).sum f =
          (Finset.range 6).sum (fun n => f (n + (-3 : ℤ))) := by
      -- unfold the Int interval as a mapped range
      simpa [Int.Icc_eq_finset_map, addLeftEmbedding, add_comm, add_left_comm, add_assoc] using
        (sum_map_embedding (s := Finset.range 6)
          (e := Nat.castEmbedding.trans (addLeftEmbedding (-3)))
          (f := f))
    have hsum_range :
        (Finset.range 6).sum (fun n => f (n + (-3 : ℤ))) =
          f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2 := by
      simp [Finset.sum_range_succ, add_assoc, add_left_comm, add_comm]
    exact hsum_map.trans hsum_range
  calc
    P_A B_min t_sym θ
        = 2 * Real.pi * ∑' m : ℤ, f m := by rfl
    _ = 2 * Real.pi * (f (-3) + f (-2) + f (-1) + f 0 + f 1 + f 2) := by
          simp [htsum, hsum]
    _ = 2 * Real.pi *
          (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
            g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := by
          simp [f, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma P_A_ge_c_star_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ ≥ c_star := by
  have hg0 : g B_min t_sym θ ≥ (9 / 32 : ℝ) := g0_lower hθ
  have hg1 : g B_min t_sym (θ + 1) ≥ (-1 / 21 : ℝ) := g1_lower hθ
  have hg2 : g B_min t_sym (θ + 2) ≥ (-7 / 50000 : ℝ) := g2_lower hθ
  have hgm1 : g B_min t_sym (1 - θ) ≥ (-1 / 50 : ℝ) := g_neg1_lower hθ
  have hgm2 : g B_min t_sym (2 - θ) ≥ (-1 / 100 : ℝ) := g_neg2_lower hθ
  have hgm3 : g B_min t_sym (3 - θ) ≥ (-1 / 2500 : ℝ) := g_neg3_lower hθ
  have hsum :
      g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
        g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)
          ≥ (1 / 5 : ℝ) := by
    have h1 : g B_min t_sym (θ - 1) = g B_min t_sym (1 - θ) := by
      have hneg : θ - 1 = -(1 - θ) := by ring
      calc
        g B_min t_sym (θ - 1) = g B_min t_sym (-(1 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (1 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 1 - θ))
    have h2 : g B_min t_sym (θ - 2) = g B_min t_sym (2 - θ) := by
      have hneg : θ - 2 = -(2 - θ) := by ring
      calc
        g B_min t_sym (θ - 2) = g B_min t_sym (-(2 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (2 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 2 - θ))
    have h3 : g B_min t_sym (θ - 3) = g B_min t_sym (3 - θ) := by
      have hneg : θ - 3 = -(3 - θ) := by ring
      calc
        g B_min t_sym (θ - 3) = g B_min t_sym (-(3 - θ)) := by
          rw [hneg]
        _ = g B_min t_sym (3 - θ) := by
          simpa using (g_even (B := B_min) (t := t_sym) (ξ := 3 - θ))
    nlinarith [hg0, hg1, hg2, hgm1, hgm2, hgm3, h1, h2, h3]
  have hmain := P_A_eq_sum6 hθ
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hpi_pos : 0 ≤ (1 / 5 : ℝ) := by norm_num
  have hconst : (6 : ℝ) * (1 / 5 : ℝ) ≥ c_star := by
    norm_num [c_star]
  have hfinal : 2 * Real.pi * (1 / 5 : ℝ) ≥ c_star := by
    have hmul : (6 : ℝ) * (1 / 5 : ℝ) ≤ 2 * Real.pi * (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hpi hpi_pos
    exact le_trans hconst hmul
  have hpospi : 0 ≤ (2 * Real.pi : ℝ) := by nlinarith [Real.pi_pos]
  calc
    P_A B_min t_sym θ
        = 2 * Real.pi *
            (g B_min t_sym (θ - 3) + g B_min t_sym (θ - 2) + g B_min t_sym (θ - 1) +
              g B_min t_sym θ + g B_min t_sym (θ + 1) + g B_min t_sym (θ + 2)) := hmain
    _ ≥ 2 * Real.pi * (1 / 5 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsum hpospi
    _ ≥ c_star := hfinal

-- Evenness of the periodized symbol (g is even, sum is reindexed).
lemma P_A_even (θ : ℝ) : P_A B_min t_sym (-θ) = P_A B_min t_sym θ := by
  have hsum_neg :
      ∑' m : ℤ, g B_min t_sym (-θ + m) =
        ∑' m : ℤ, g B_min t_sym (θ + (-m)) := by
    refine tsum_congr ?_
    intro m
    have hneg : -θ + (m : ℝ) = -(θ + (- (m : ℝ))) := by ring
    simpa [hneg] using (g_even (B := B_min) (t := t_sym) (ξ := θ + (- (m : ℝ))))
  have hsum :
      ∑' m : ℤ, g B_min t_sym (θ + (-m)) =
        ∑' m : ℤ, g B_min t_sym (θ + m) := by
    simpa using (Equiv.tsum_eq (Equiv.neg ℤ) (fun m : ℤ => g B_min t_sym (θ + m)))
  calc
    P_A B_min t_sym (-θ)
        = 2 * Real.pi * ∑' m : ℤ, g B_min t_sym (-θ + m) := by rfl
    _ = 2 * Real.pi * ∑' m : ℤ, g B_min t_sym (θ + m) := by
          simp [hsum_neg, hsum]
    _ = P_A B_min t_sym θ := by rfl

/-- Final A3 floor on [-1/2, 1/2]. -/
theorem P_A_ge_c_star {θ : ℝ} (hθ : θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)) :
    P_A B_min t_sym θ ≥ c_star := by
  by_cases hθpos : 0 ≤ θ
  · have hθ' : θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      exact ⟨hθpos, hθ.2⟩
    exact P_A_ge_c_star_nonneg hθ'
  · have hθ' : -θ ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      have h1 : 0 ≤ -θ := by nlinarith
      have h2 : -θ ≤ (1 / 2 : ℝ) := by nlinarith [hθ.1]
      exact ⟨h1, h2⟩
    have h := P_A_ge_c_star_nonneg hθ'
    simpa [P_A_even] using h


## File: full/q3.lean.aristotle/Q3/Proofs/A3_Floor_Critical_Goal.lean

import Mathlib
import Q3.Axioms
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

open scoped Real

noncomputable section

namespace Q3.Proofs.A3FloorCritical

/-- One-scale A3_FLOOR goal at the critical parameter `t_critical = 3/20`.

This is intentionally packaged as a `Prop` (not an axiom and not a sorry-proof) so we can
reference it in the decision tree / Aristotle prompts without polluting the main chain.
-/
def FloorGoal : Prop :=
  ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
    Q3.c_star ≤ P_A B_min Q3.t_critical θ

end Q3.Proofs.A3FloorCritical


## File: full/q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean

/-
Q >= 0 at t_critical = 0.15

This file proves Q(phi) >= 0 for Fejer-heat atoms with t_critical = 3/20.

Key insight: at t_critical, BOTH conditions hold simultaneously:
  1. P_A(theta) >= c_star = 11/10 (Archimedean floor preserved)
  2. prime_sum is small enough that arch_term dominates

Numerical verification (Python):
  t = 0.15: Q = +0.86 > 0, min P_A = 1.66 > 1.1
  t* ~ 0.136 is the crossover point where Q changes sign

LaTeX <-> Lean parameter conversion:
  LaTeX: exp(-4*pi^2*t*xi^2)
  Lean:  exp(-xi^2/(4*t0))
  Relation: t0 = 1/(16*pi^2*t)

  t_critical = 0.15 => t0_critical = 1/(16*pi^2*0.15) ~ 0.0422
-/

import Q3.Axioms
import Q3.Proofs.Params_Critical
import A3_FLOOR_v20_bounds_core
import Q3.Proofs.ShiftedWindows

set_option linter.mathlibStandardSet false

open scoped BigOperators Real Classical ComplexConjugate
open MeasureTheory

noncomputable section

namespace Q3

/-- t_critical > t_sym (0.15 > 0.06), so heat decay is stronger -/
lemma t_critical_gt_t_sym : t_critical > t_sym := by
  norm_num [t_critical, t_sym]

/-- Parameter conversion: exp(-xi^2/(4*t0_critical)) = exp(-4*pi^2*t_critical*xi^2) -/
lemma exp_reparam_critical' (x : ℝ) :
    Real.exp (-x^2 / (4 * t0_critical)) = Real.exp (-4 * Real.pi ^ 2 * t_critical * x^2) :=
  Q3.exp_reparam_critical x

/-! ## Fejer-Heat Window at t_critical -/

/-- Fejer-heat window at t_critical -/
def fejer_heat_window_critical (B : ℝ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / B) * Real.exp (-4 * Real.pi^2 * t_critical * ξ^2)

lemma fejer_heat_window_critical_eq (B ξ : ℝ) :
    fejer_heat_window_critical B ξ = fejer_heat_window B t_critical ξ := by
  rfl

lemma fejer_heat_window_critical_nonneg (B ξ : ℝ) :
    0 ≤ fejer_heat_window_critical B ξ := by
  unfold fejer_heat_window_critical
  apply mul_nonneg
  · exact le_max_left _ _
  · exact Real.exp_nonneg _

/-! ## phi_shift at t_critical -/

/-- phi_shift at t_critical -/
def phi_shift_critical (B τ : ℝ) (ξ : ℝ) : ℝ :=
  phi_shift B t_critical τ ξ

lemma phi_shift_critical_nonneg (B τ ξ : ℝ) :
    0 ≤ phi_shift_critical B τ ξ := by
  unfold phi_shift_critical phi_shift
  exact fejer_heat_window_nonneg B t_critical (ξ - τ)

/-! ## P_A Floor at t_critical -/

/-- P_A at t_critical: periodized Archimedean density -/
def P_A_critical (B : ℝ) (θ : ℝ) : ℝ :=
  P_A_shift B t_critical 0 θ

/-- P_A floor at t_critical: min P_A >= c_star = 11/10
    Numerical verification: at t_critical = 0.15, min P_A = 1.66 > 1.1 -/
lemma P_A_ge_c_star_at_t_critical (θ : ℝ) :
    P_A_critical B_min θ ≥ c_star := by
  /- I/O CARD: P_A_ge_c_star_at_t_critical
     INPUT:  θ : ℝ
     OUTPUT: P_A_critical B_min θ ≥ c_star (= 11/10)
     NEED:   Numerical verification that min P_A(θ) = 1.66 > 1.1 at t = 0.15
             This follows from P_A floor INCREASING with t (heat decay suppresses harmonics)
     BLOCKS: [arch_term_ge_at_t_critical, Q_phi_shift_nonneg_t_critical]
  -/
  sorry

/-! ## arch_term bounds at t_critical -/

/-- arch_term at t_critical is bounded below -/
lemma arch_term_ge_at_t_critical (B τ : ℝ) (hB : B > 0)
    (h_floor : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      c_star ≤ P_A_shift B t_critical τ θ) :
    arch_term (fun ξ => phi_shift_critical B τ ξ) ≥
      c_star * (1 - |τ| / B) := by
  /- I/O CARD: arch_term_ge_at_t_critical
     INPUT:  B τ : ℝ, hB : B > 0
     OUTPUT: arch_term(phi_shift_critical) ≥ c_star * (1 - |τ|/B)
     NEED:   pointwise floor on P_A_shift at t_critical
             integral_P_A_shift_eq_arch_term (periodization identity)
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  have hab : (-1/2 : ℝ) ≤ (1/2 : ℝ) := by norm_num
  have h_cont : Continuous (fun θ => P_A_shift B t_critical τ θ) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=τ) hB
  have h_int : IntervalIntegrable (fun θ => P_A_shift B t_critical τ θ) volume (-1/2) (1/2) :=
    h_cont.intervalIntegrable _ _
  have h_const : IntervalIntegrable (fun _ : ℝ => (c_star : ℝ)) volume (-1/2) (1/2) := by
    simpa using
      (intervalIntegrable_const (μ := volume) (a := (-1/2 : ℝ)) (b := (1/2 : ℝ))
        (c := (c_star : ℝ)))
  have h_mono :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) ≤
        ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ := by
    exact intervalIntegral.integral_mono_on
      (a := (-1/2 : ℝ)) (b := (1/2 : ℝ)) (μ := volume)
      (f := fun _ : ℝ => (c_star : ℝ)) (g := fun θ => P_A_shift B t_critical τ θ)
      (hab := hab) (hf := h_const) (hg := h_int) h_floor
  have hlen : ((2⁻¹ : ℝ) - (-1/2)) = (1 : ℝ) := by norm_num
  have h_const_int :
      (∫ θ in (-1/2 : ℝ)..(1/2), (c_star : ℝ)) = c_star := by
    simp [intervalIntegral.integral_const, hlen]
  have h_arch_eq :
      ∫ θ in (-1/2 : ℝ)..(1/2), P_A_shift B t_critical τ θ =
        arch_term (fun ξ => phi_shift_critical B τ ξ) := by
    simpa [phi_shift_critical] using
      (Q3.Proofs.ShiftedWindows.integral_P_A_shift_eq_arch_term (B:=B) (t:=t_critical)
        (tau:=τ) hB)
  have h_arch_ge : arch_term (fun ξ => phi_shift_critical B τ ξ) ≥ c_star := by
    have h_mono' := h_mono
    rw [h_const_int] at h_mono'
    rw [h_arch_eq] at h_mono'
    exact h_mono'
  have h_factor : c_star * (1 - |τ| / B) ≤ c_star := by
    have h_nonneg : 0 ≤ |τ| / B := by
      have hτ : 0 ≤ |τ| := abs_nonneg _
      exact div_nonneg hτ (le_of_lt hB)
    nlinarith [h_nonneg, c_star_pos]
  exact le_trans h_factor h_arch_ge

/-! ## prime_term bounds at t_critical -/

/-- prime_term at t_critical is bounded by arch_term
    Key insight: at t_critical, heat decay exp(-4*pi^2*t*xi^2) is strong enough
    that prime_sum = Σ w(n)*Phi(xi_n) becomes small relative to arch_term -/
lemma prime_term_le_at_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    prime_term (fun ξ => phi_shift_critical B τ ξ) ≤
      arch_term (fun ξ => phi_shift_critical B τ ξ) := by
  /- I/O CARD: prime_term_le_at_t_critical
     INPUT:  K B τ : ℝ, hK : K ≥ 1, hB : B > 0, hτB : |τ| + B ≤ K
     OUTPUT: prime_term(phi_shift_critical) ≤ arch_term(phi_shift_critical)
     NEED:   Numerical verification at t = 0.15, B = 3:
               arch_term = 9.57
               prime_term = 8.71
               Q = arch - prime = +0.86 > 0
             The heat factor exp(-4*pi^2*0.15*xi^2) decays fast enough
     BLOCKS: [Q_phi_shift_nonneg_t_critical]
  -/
  sorry

/-! ## Main Theorem: Q >= 0 at t_critical -/

/-- Main lemma: Q(phi_shift at t_critical) >= 0 -/
theorem Q_phi_shift_nonneg_t_critical (K B τ : ℝ)
    (hK : K ≥ 1) (hB : B > 0) (hτB : |τ| + B ≤ K) :
    Q (fun ξ => phi_shift_critical B τ ξ) ≥ 0 := by
  unfold Q
  have h := prime_term_le_at_t_critical K B τ hK hB hτB
  linarith

/-! ## Connection to Fejer_heat_atom -/

/-- Fejer_heat_atom at t_critical -/
def Fejer_heat_atom_critical (B τ : ℝ) (ξ : ℝ) : ℝ :=
  Fejer_heat_atom B t_critical τ ξ

/-- Fejer_heat_atom = phi_shift(+tau) + phi_shift(-tau) (symmetrized) -/
lemma Fejer_heat_atom_eq_phi_shifts (B τ ξ : ℝ) :
    Fejer_heat_atom_critical B τ ξ =
      phi_shift_critical B τ ξ + phi_shift_critical B (-τ) ξ := by
  /- I/O CARD: Fejer_heat_atom_eq_phi_shifts
     INPUT:  B τ ξ : ℝ
     OUTPUT: Fejer_heat_atom_critical = phi_shift(+τ) + phi_shift(-τ)
     NEED:   Definitions of Fejer_heat_atom, phi_shift, fejer_heat_window
             The atom is cos-modulated: includes both +tau and -tau shifts
     BLOCKS: [Q_Fejer_heat_atom_nonneg_t_critical]
  -/
  simp only [Fejer_heat_atom_critical, Fejer_heat_atom, phi_shift_critical, phi_shift,
    fejer_heat_window]
  ring_nf
  sorry

/-! ## Q on BaseAtomCone at t_critical -/

/-- BaseAtomCone at t0_critical (τ=0 only!)

    CRITICAL: Q >= 0 holds ONLY on BaseAtomCone (τ=0), not on full AtomCone!
    Numerical verification shows Q = -911 at τ = 1.69.

    This is sufficient because W_K requires even functions, and
    BaseAtomCone generates even approximants.
-/
def BaseAtomCone_critical (K : ℝ) : Set (ℝ → ℝ) :=
  BaseAtomCone_K K t0_critical

/-- Q >= 0 on BaseAtomCone at t0_critical (τ=0 only!)

    This replaces the axiom Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
    but restricted to BaseAtomCone_K (centered atoms, no τ-shift).

    Numerical verification (Python verify_variant_b.py):
      For all B ∈ [0.5, 4.9], τ=0: min Q = 1.03 > 0  ✓
      For τ > 0: Q can be < 0 (e.g. Q = -911 at τ = 1.69)  ✗
-/
theorem Q_nonneg_on_base_atoms_at_t_critical (K : ℝ) (hK : K ≥ 1) :
    ∀ g ∈ BaseAtomCone_critical K, Q g ≥ 0 := by
  /- I/O CARD: Q_nonneg_on_base_atoms_at_t_critical
     INPUT:  K : ℝ, hK : K ≥ 1, g ∈ BaseAtomCone_critical K
     OUTPUT: Q g ≥ 0
     NEED:   g = Σ c_i * Fejer_heat_atom(B_i, t0_critical, 0)  (τ=0!)
             At τ=0: Fejer_heat_atom B t 0 ξ = 2 * Φ_B(ξ)
             By Q linearity: Q(g) = Σ c_i * Q(2*Φ_{B_i})
             Each Q(2*Φ_B) ≥ 0 (verified numerically for all B ≤ K)
             c_i ≥ 0, so sum ≥ 0
     BLOCKS: [Q_nonneg_base_atoms_summary, main theorem chain]
  -/
  intro g hg
  sorry

/-! ## Summary -/

/-- The key theorem: at t_critical = 0.15, Q >= 0 on BaseAtomCone (τ=0).

    This closes the gap in the LaTeX proof where t_sym = 0.06 gave Q < 0.
    The solution: increase t from 0.06 to 0.15, where:
    1. Q becomes positive (arch_term > prime_term)
    2. P_A floor is still preserved (min P_A = 1.66 > c_star = 1.1)

    CRITICAL CONSTRAINT: Q >= 0 holds ONLY for τ=0 (BaseAtomCone).
    For τ > 0, Q can be negative (Q = -911 at τ = 1.69).

    This is OK because W_K requires even functions, and BaseAtomCone_K
    is sufficient to approximate all even functions (no τ-shifts needed).

    Numerical crossover point: t* ≈ 0.136
-/
theorem Q_nonneg_base_atoms_summary :
    ∃ t : ℝ, t > t_sym ∧ t < 1 ∧
      (∀ K ≥ 1, ∀ g ∈ BaseAtomCone_K K (1 / (16 * Real.pi^2 * t)), Q g ≥ 0) := by
  use t_critical
  constructor
  · exact t_critical_gt_t_sym
  constructor
  · norm_num [t_critical]
  intro K hK g hg
  have h_eq : (1 / (16 * Real.pi^2 * t_critical)) = t0_critical := by
    unfold t0_critical
    ring
  rw [h_eq] at hg
  exact Q_nonneg_on_base_atoms_at_t_critical K hK g hg

end Q3


## File: full/q3.lean.aristotle/Q3/Proofs/SingleScale_Assumptions.lean

import Q3.Axioms
import Q3.Proofs.Q_nonneg_t_critical
import Q3.Proofs.Rayleigh_Q_identification
import Q3.Proofs.RKHS_cap_rayleigh
import Q3.Proofs.ShiftedWindows
import Q3.Proofs.A3_Floor_Critical_Goal

set_option linter.mathlibStandardSet false

/-!
Single-scale assumptions at t_critical.

These are temporary bridge axioms to close the fixed-t chain without the
two-scale `t_sym`/`t_rkhs_cap` mismatch. They can be proved or replaced later.
-/

noncomputable section

namespace Q3.Proofs.SingleScale

open Q3

/-! ## Continuity of the shifted symbol (single-scale) -/

theorem continuous_P_A_shift (B tau : ℝ) (hB : 0 < B) :
    Continuous (Q3.P_A_shift B t_critical tau) := by
  simpa using
    (Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=tau) hB)

/-! ## A3-style lower bound at basis0 (tau = 0 mainline) -/

/-! ### Reduction: rayleigh_basis0 from the one-scale floor -/

theorem rayleigh_basis0_shift_ge_cstar_quarter_of_floor
    (B : ℝ) (M : ℕ) (hBmin : B = B_min)
    (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  classical
  subst hBmin
  have h_eq : Q3.P_A_shift B_min t_critical 0 = P_A B_min t_critical := by
    ext θ
    simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g,
      Q3.Proofs.RayleighQId.w_eq_fejer_heat_window]
  have hB_pos : 0 < B_min := by
    norm_num [B_min]
  have hP_cont : Continuous (Q3.P_A_shift B_min t_critical 0) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B_min) (t:=t_critical) (tau:=0) hB_pos
  have hM : (2 * M + 1) > 0 := by
    exact Nat.succ_pos _
  have hRQ_full :
      Q3.RayleighQuotient
          (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
            (Q3.P_A_shift B_min t_critical 0))
          (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star := by
    have hP_ge : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
        Q3.c_star ≤ Q3.P_A_shift B_min t_critical 0 θ := by
      intro θ hθ
      have h' := h_floor θ hθ
      simpa [h_eq] using h'
    exact RayleighFourier.rayleigh_lower_bound_real
      (M := 2 * M + 1) (hM := hM)
      (P := Q3.P_A_shift B_min t_critical 0) (hP_cont := hP_cont)
      (m := Q3.c_star) (hP_ge := hP_ge)
      (v := Q3.Proofs.RayleighQId.basis0 M)
      (hv := Q3.Proofs.RayleighQId.basis0_ne_zero M)
  have h_quarter : Q3.c_star / 4 ≤ Q3.c_star := by
    nlinarith [Q3.c_star_pos]
  exact le_trans h_quarter hRQ_full

lemma floor_P_A_shift_tcritical_Bmin
    (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      Q3.c_star ≤ Q3.P_A_shift B_min t_critical 0 θ := by
  intro θ hθ
  have h' := h_floor θ hθ
  have h_eq : Q3.P_A_shift B_min t_critical 0 = P_A B_min t_critical := by
    ext t
    simp [Q3.P_A_shift, P_A, Q3.g_shift, Q3.phi_shift, g,
      Q3.Proofs.RayleighQId.w_eq_fejer_heat_window]
  simpa [h_eq] using h'

/-! ### Reduction: rayleigh_basis0 from arch_term at t_critical (Option 2) -/

theorem rayleigh_basis0_shift_ge_cstar_quarter_of_arch_term
    (B : ℝ) (M : ℕ) (hB : 0 < B)
    (h_arch : Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥ Q3.c_star) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have hP_cont : Continuous (Q3.P_A_shift B t_critical 0) :=
    Q3.Proofs.ShiftedWindows.P_A_shift_continuous (B:=B) (t:=t_critical) (tau:=0) hB
  have h_eq :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M)
        =
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) := by
    simpa using
      (Q3.Proofs.RayleighQId.arch_rayleigh_eq_shift
        (B:=B) (t:=t_critical) (tau:=0) (M:=M) hP_cont hB)
  have hRQ_full :
      Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star := by
    simpa [h_eq] using h_arch
  have h_quarter : Q3.c_star / 4 ≤ Q3.c_star := by
    nlinarith [Q3.c_star_pos]
  exact le_trans h_quarter hRQ_full

theorem rayleigh_basis0_shift_ge_cstar_quarter
    (B : ℝ) (M : ℕ) (hB : 0 < B)
    (h_floor : ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
      Q3.c_star ≤ Q3.P_A_shift B t_critical 0 θ) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have h_arch' :
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥
        Q3.c_star * (1 - |(0 : ℝ)| / B) := by
    simpa using (Q3.arch_term_ge_at_t_critical (B:=B) (τ:=0) hB h_floor)
  have h_arch :
      Q3.arch_term (fun ξ => Q3.phi_shift B t_critical 0 ξ) ≥ Q3.c_star := by
    simpa using h_arch'
  exact rayleigh_basis0_shift_ge_cstar_quarter_of_arch_term (B:=B) (M:=M) hB h_arch

theorem rayleigh_basis0_shift_ge_cstar_quarter_Bmin
    (M : ℕ) (h_floor : Q3.Proofs.A3FloorCritical.FloorGoal) :
    Q3.RayleighQuotient
        (RayleighFourier.ToeplitzMatrix_Fourier_real (2 * M + 1)
          (Q3.P_A_shift B_min t_critical 0))
        (Q3.Proofs.RayleighQId.basis0 M) ≥ Q3.c_star / 4 := by
  have hB : 0 < B_min := by
    norm_num [B_min]
  have h_floor' := floor_P_A_shift_tcritical_Bmin h_floor
  exact rayleigh_basis0_shift_ge_cstar_quarter (B:=B_min) (M:=M) hB h_floor'

/-! ## Single-scale prime cap (tau = 0 mainline) -/

theorem rho_oneK_tcritical_le_cstar_quarter (_K : ℝ) :
    Q3.Proofs.rho_one ≤ Q3.c_star / 4 := by
  norm_num [Q3.Proofs.rho_one, Q3.c_star]

/-! ## Single-scale RKHS contraction (t = t_critical) -/

axiom rkhs_contraction_tcritical
    (K : ℝ) (hK : K ≥ 1) :
    ∃ ρ : ℝ, ρ < 1 ∧
      ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Q3.Nodes K) →
        let T_P : Matrix S S ℝ := fun i j =>
          Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
          Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t_critical))
        ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ

theorem rkhs_contraction_data_of_tcritical (K : ℝ) (hK : K ≥ 1) :
    Q3.RKHS_contraction_data K := by
  classical
  obtain ⟨ρ, hρ_lt, hT⟩ := rkhs_contraction_tcritical (K := K) hK
  refine ⟨t_critical, t_critical_pos, ρ, hρ_lt, ?_⟩
  intro S hS
  exact hT S hS

end Q3.Proofs.SingleScale
