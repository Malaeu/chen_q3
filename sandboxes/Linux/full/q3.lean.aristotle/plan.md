⏺ План обновлён! Вот краткая сводка что будем делать:

  Summary

  Цель: Разрезать Q_nonneg_on_W_K_axiom (ядерная бомба) на честную лесенку

  6 шагов:

| #    | Что делаем                                                   | Файл             |
| ---- | ------------------------------------------------------------ | ---------------- |
| 1    | Добавить W_K (с ContinuousOn!) + AtomCone_K                  | Basic/Defs.lean  |
| 2    | Удалить Q_nonneg_on_W_K_axiom, добавить A1_density_WK_axiom + Q_nonneg_on_atoms_axiom | Axioms.lean      |
| 3    | СОЗДАТЬ T5_Transfer.lean с доказательством T5_transfer       | T5_Transfer.lean |
| 4    | Использовать T5_transfer вместо axiom                        | Main.lean        |
| 5    | Обновить проверки                                            | CheckAxioms.lean |
| 6    | Build & verify                                               | lake build       |

  Ключевой момент: T5 будет theorem (не axiom!) — чистая топология/анализ.

  Готов к имплементации?
                                                                                                          
⏺ User approved Claude's plan
  ⎿  Plan saved to: ~/.claude/plans/hashed-cuddling-hennessy.md · /plan to edit
     Q3 Lean Formalization: Axiom Decomposition Plan

     Current Problem
    
     Q_nonneg_on_W_K_axiom = "весь Q3 в одном глотке" — ядерная бомба!
    
     Сейчас #print axioms RH_of_Weil_and_Q3 показывает:
     - Weil_criterion (Tier-1, OK)
     - Q_nonneg_on_W_K_axiom (Tier-2, НЕ ОК — слишком жирно!)
    
     ---
     Goal: Разрезать Q_nonneg_on_W_K_axiom на честную лесенку
    
     Было:
     Weil_criterion + Q_nonneg_on_W_K_axiom → RH
    
     Станет:
     Weil_criterion
         + A1_density_WK_axiom      (плотность атомов)
         + Q_Lipschitz_on_W_K       (липшицевость)
         + Q_nonneg_on_atoms_axiom  (Q ≥ 0 на атомах)
         + T5_transfer (THEOREM!)   (перенос с атомов на весь W_K)
     → RH
    
     ---
     Step 0: Fix W_K definition
    
     Проблема текущего Weil_cone_K:
    
     def Weil_cone_K (K : ℝ) : Set (ℝ → ℝ) :=
       {Φ | IsEven Φ ∧ IsNonneg Φ ∧ Function.support Φ ⊆ Set.Icc (-K) K}
     Нет ContinuousOn! Без этого sup-норма не определена корректно.
    
     Новое определение W_K:
    
     /-- W_K: space for T5 transfer theorem -/
     def W_K (K : ℝ) : Set (ℝ → ℝ) :=
       {Φ | ContinuousOn Φ (Set.Icc (-K) K) ∧
            Function.support Φ ⊆ Set.Icc (-K) K ∧
            IsEven Φ ∧
            IsNonneg Φ}
    
     ---
     Step 1: Define AtomCone_K
    
     /-- Atom cone: Fejér×heat atoms with support in [-K,K] -/
     def AtomCone_K (K : ℝ) : Set (ℝ → ℝ) :=
       { g | ∃ (n : ℕ) (c : Fin n → ℝ) (B t : Fin n → ℝ) (τ : Fin n → ℝ),
             (∀ i, c i ≥ 0) ∧
             (∀ i, B i > 0) ∧
             (∀ i, t i > 0) ∧
             (∀ i, |τ i| ≤ K) ∧
             (∀ i, B i ≤ K) ∧  -- NEW: ensures support ⊆ [-K,K]
             (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) (t i) (τ i) x) ∧
             g ∈ W_K K }  -- NEW: explicitly require g ∈ W_K
    
     ---
     Step 2: New Axiom Structure (replacing Q_nonneg_on_W_K_axiom)
    
     A1: Density (updated)
    
     axiom A1_density_WK_axiom : ∀ (K : ℝ) (hK : K > 0),
       ∀ Φ ∈ W_K K, ∀ ε > 0,
         ∃ g ∈ AtomCone_K K,  -- g is in atom cone AND in W_K
           sSup {|Φ x - g x| | x ∈ Set.Icc (-K) K} < ε
    
     A2: Lipschitz (keep as is, but on W_K)
    
     axiom Q_Lipschitz_on_W_K : ∀ (K : ℝ) (hK : K > 0),
       ∃ L > 0, ∀ Φ₁ Φ₂ ∈ W_K K,
         |Q Φ₁ - Q Φ₂| ≤ L * sSup {|Φ₁ x - Φ₂ x| | x ∈ Set.Icc (-K) K}
    
     Atoms: Q ≥ 0 on atoms (NEW, replaces the nuclear bomb)
    
     axiom Q_nonneg_on_atoms_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
       ∀ g ∈ AtomCone_K K, Q g ≥ 0
    
     ---
     Step 3: T5 as THEOREM (not axiom!)
    
     /-- T5: Transfer positivity from dense atoms to all of W_K -/
     theorem T5_transfer (K : ℝ) (hK : K ≥ 1) :
         ∀ Φ ∈ W_K K, Q Φ ≥ 0 := by
       intro Φ hΦ
       -- A1: Get approximating sequence from AtomCone_K
       -- A2: Q is Lipschitz, so Q(Φ) = lim Q(g_n)
       -- Atoms: Q(g_n) ≥ 0 for all n
       -- Conclusion: Q(Φ) ≥ 0 by limit preservation
       sorry  -- TO BE PROVEN (pure analysis/topology)
    
     Why T5 can be proven:
     - Dense approximation + Lipschitz continuity + limit of nonnegatives ≥ 0
     - This is standard analysis, no number theory needed!
    
     ---
     Step 4: Update Main.lean
    
     theorem Q_nonneg_on_W_K (K : ℝ) (hK : K ≥ 1) :
         ∀ Φ ∈ W_K K, Q Φ ≥ 0 :=
       T5_transfer K hK  -- Uses T5 theorem
    
     -- Then same logic as before for full Weil cone
    
     ---
     Step 5: Remove Q_nonneg_on_W_K_axiom
    
     Delete from Axioms.lean:
     -- DELETE THIS:
     axiom Q_nonneg_on_W_K_axiom : ∀ (K : ℝ) (hK : K ≥ 1),
       ∀ Φ ∈ Weil_cone_K K, Q Φ ≥ 0
    
     ---
     New Axiom Hierarchy
    
     Tier-1 (Classical, 1911-1999):
    
     | #    | Axiom              | Citation            |
     |------|--------------------|---------------------|
     | T1.1 | Weil_criterion     | Weil 1952           |
     | T1.2 | explicit_formula   | Guinand 1948        |
     | T1.3 | a_star_pos         | Titchmarsh 1986     |
     | T1.4 | Szego_Bottcher_*   | Szegő 1958          |
     | T1.5 | Schur_test         | Schur 1911          |
     | T1.6 | c_arch_pos         | (follows from T1.3) |
     | T1.7 | eigenvalue_le_norm | Standard LA         |
    
     Tier-2 (Q3 Paper):
    
     | #    | Axiom                   | What it says          |
     |------|-------------------------|-----------------------|
     | T2.1 | A1_density_WK_axiom     | Atoms dense in W_K    |
     | T2.2 | Q_Lipschitz_on_W_K      | Q is Lipschitz        |
     | T2.3 | RKHS_contraction_axiom  | ‖T_P‖ < 1             |
     | T2.4 | T_P_row_sum_bound_axiom | Row sums bounded      |
     | T2.5 | S_K_small_axiom         | Geometric decay       |
     | T2.6 | A3_bridge_axiom         | Toeplitz-Symbol gap   |
     | T2.7 | Q_nonneg_on_atoms_axiom | Q ≥ 0 on atoms (NEW!) |
    
     Tier-3 (Proven in Lean):
    
     | Theorem               | Dependencies                 |
     |-----------------------|------------------------------|
     | T5_transfer           | A1 + A2 + Atoms              |
     | Q_nonneg_on_W_K       | T5_transfer                  |
     | Q_nonneg_on_Weil_cone | Q_nonneg_on_W_K              |
     | RH_of_Weil_and_Q3     | Weil + Q_nonneg_on_Weil_cone |
    
     ---
     Files to Modify
    
     | File             | Action                                                                         |
     |------------------|--------------------------------------------------------------------------------|
     | Basic/Defs.lean  | Add W_K, AtomCone_K                                                            |
     | Axioms.lean      | Remove Q_nonneg_on_W_K_axiom, add A1_density_WK_axiom, Q_nonneg_on_atoms_axiom |
     | T5_Transfer.lean | CREATE: Prove T5_transfer theorem                                              |
     | Main.lean        | Use T5_transfer instead of axiom                                               |
     | CheckAxioms.lean | Update axiom list                                                              |
    
     ---
     Implementation Steps (TODO)
    
     Step 1: Update Basic/Defs.lean
    
     - Add W_K definition with ContinuousOn
     - Add AtomCone_K definition
     - Add helper: AtomCone_subset_W_K lemma
    
     Step 2: Update Axioms.lean
    
     - Remove Q_nonneg_on_W_K_axiom
     - Add A1_density_WK_axiom (updated form)
     - Add Q_nonneg_on_atoms_axiom
    
     Step 3: Create T5_Transfer.lean
    
     - Prove nonneg_of_dense_approx (general topology lemma)
     - Prove T5_transfer using A1, A2, Atoms
     - Prove Q_nonneg_on_W_K as corollary
    
     Step 4: Update Main.lean
    
     - Remove usage of Q_nonneg_on_W_K_axiom
     - Use T5_transfer theorem
     - Verify #print axioms shows new hierarchy
    
     Step 5: Update CheckAxioms.lean
    
     - Add new axiom checks
     - Remove old axiom check
    
     Step 6: Build & Verify
    
     - lake build passes
     - #print axioms RH_of_Weil_and_Q3 shows clean hierarchy
     - No sorry statements
    
     ---
     Expected #print axioms Output (After)
    
     'RH_of_Weil_and_Q3' depends on axioms:
     [propext, Classical.choice, Quot.sound,
      Q3.Weil_criterion,           -- Tier-1
      Q3.A1_density_WK_axiom,      -- Tier-2 (density)
      Q3.Q_Lipschitz_on_W_K,       -- Tier-2 (Lipschitz)
      Q3.Q_nonneg_on_atoms_axiom]  -- Tier-2 (Q ≥ 0 on atoms)
    
     Much cleaner than single Q_nonneg_on_W_K_axiom!
    
     ---
     Dependency Graph (New)
    
     ┌─────────────────────────────────────────────────────┐
     │ Tier-1: Weil_criterion (established 1952)           │
     └─────────────────────────────────────────────────────┘
                              │
                              ▼
     ┌─────────────────────────────────────────────────────┐
     │ Tier-2: Q3 Paper Axioms                             │
     │                                                     │
     │  A1_density_WK_axiom ─────┐                         │
     │                           │                         │
     │  Q_Lipschitz_on_W_K ──────┼──► T5_transfer (THM!)   │
     │                           │          │              │
     │  Q_nonneg_on_atoms_axiom ─┘          │              │
     │                                      ▼              │
     │  (RKHS/A3 axioms ──────► Q_nonneg_on_atoms)        │
     └─────────────────────────────────────────────────────┘
                              │
                              ▼
     ┌─────────────────────────────────────────────────────┐
     │ Tier-3: Lean Theorems                               │
     │                                                     │
     │  T5_transfer ──► Q_nonneg_on_W_K ──► Q_nonneg_on_Weil_cone
     │                                              │      │
     │                                              ▼      │
     │                                    RH_of_Weil_and_Q3│
     └─────────────────────────────────────────────────────┘
    
     ---
     Risk Assessment
    
     | Step           | Risk   | Mitigation                 |
     |----------------|--------|----------------------------|
     | W_K definition | LOW    | Standard topology          |
     | A1 update      | LOW    | Same idea, better contract |
     | T5 proof       | MEDIUM | May need Mathlib lemmas    |
     | Build          | LOW    | Incremental changes        |
    
     ---
     Success Criteria
    
     ✅ After completion:
     - Q_nonneg_on_W_K_axiom GONE
     - T5 is a THEOREM (not axiom)
     - #print axioms shows A1, A2, Atoms (not nuclear bomb)
     - lake build passes
     - 0 sorry statements

⏺ ⭐IDDQD⭐✨GoD MoDe✨ 🤩ACTIVE👁️nn

  Погнали! Создаю todo list и начинаю имплементацию: