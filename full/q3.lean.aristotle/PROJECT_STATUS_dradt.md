 Here is Claude's plan:
╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌
 Q3 → RH: Полный Proof Pipeline (TAO/PERELMAN/FEYNMAN Edition)

 ЦЕЛЬ

 Создать 100% честный proof для reviewer'а где:
 #print axioms RH_proven
 Показывает ТОЛЬКО:
 - propext, Classical.choice, Quot.sound (стандартные Lean)
 - Tier-1 аксиомы (классика из литературы: Weil, Guinand, Böttcher-Silbermann)

---
 ПРОТОКОЛ AGENTIC RUN

 КРИТИЧНО: Максимум 3 агента параллельно (экономия контекста)

 Структура каждого run:
 1. Запустить 3 агента параллельно
 2. Дождаться результатов
 3. Остальные задачи → ToDo для следующего run
 4. Commit изменения
 5. Следующий run

---
 ТЕКУЩИЙ СТАТУС (2025-12-20 update)

| Компонент                    | Статус                                                       |
| ---------------------------- | ------------------------------------------------------------ |
| Working bridges              | 4/9 (node_spacing, S_K_small, W_sum_finite, off_diag_exp_sum) |
| Sorry в коде                 | 1 (A1_density: sum_atoms_in_cone → sorryAx)                  |
| RKHS_contraction_bridge.lean | ✅ fixed (no circular axiom, uses Bridge axiom)               |

 КЛЮЧЕВОЙ ИНСАЙТ: Coordinate Rescaling (НЕ баг!)

 Standalone uses: α = log n, Q3 uses: ξ = log n/(2π)

 Это coordinate rescaling с константой c = 2π:
 α = c · ξ           (coordinate)
 t_α = c² · t_ξ      (heat parameter)
 K_α = c · K_ξ       (window)
 δ_α = c · δ_ξ       (spacing)

 ГЛАВНЫЙ ИНВАРИАНТ: δ²/(4t) не меняется при rescale!
 δ_α²/(4t_α) = (c·δ_ξ)²/(4·c²·t_ξ) = δ_ξ²/(4t_ξ)

 ⇒ Heat kernel exp(-(gap)²/(4t)) переносится без изменений!

---
 RKHS BRIDGE СПЕЦИФИКАЦИЯ (TAO/PERELMAN/FEYNMAN)

 Standalone theorem (полностью доказан!):

 -- Q3/Proofs/RKHS_contraction.lean:339-369
 theorem RKHS_contraction (K : ℝ) (hK : K ≥ 1) :
   ∃ t > 0, ∃ ρ < 1, T_P_norm K t ≤ ρ

 RKHS_rescaling.lean (✅ создан, работает):

 - c = 2 * Real.pi, c_pos
 - alpha_eq_two_pi_mul_xi - α = c · ξ
 - heat_exponent_rescale_invariant - δ²/(4t) инвариант
 - heat_exp_rescale_invariant - exp переносится
 - nodes_window_correspondence - окна соответствуют
 - delta_rescale, t_min_rescale - параметры

 RKHS_contraction_bridge.lean (✅ FIXED; сборка OK):

 Было: `exact RKHS_contraction_axiom K hK` (CIRCULAR)
 Стало: `simpa using Q3.Bridge.RKHS_contraction_data_of_bridge K hK` (OK)

 РЕШЕНИЕ:
 -- 1. Qualify standalone namespace (избежать конфликтов)
 -- standalone uses: ξ, nodes, δ_K, T_P_norm, RKHS_contraction
 -- Q3 uses: xi_n, Nodes_Q3, delta_K, etc.

 -- 2. Применить standalone к rescaled параметрам:
 have h := RKHS_contraction (2 * Real.pi * K) (by linarith : 2 * Real.pi * K ≥ 1)
 obtain ⟨t_alpha, ht_pos, ρ, hρ_lt, hbound⟩ := h

 -- 3. Обратный rescale: t_ξ := t_α / (2π)²
 use t_alpha / (2 * Real.pi)^2
 use ρ

 -- 4. Heat kernel entries совпадают через heat_exp_rescale_invariant
 -- 5. Matrix norm переносится (та же матрица!)

 "Гениальные оптимизации" (PERELMAN):

 1. Неравенства вместо равенств для δK:
   - Контракция питается только δ_actual ≥ δ_def
   - Не доказывать δ_standalone = 2π · δ_Q3
   - Доказать δ_standalone(2πK) ≥ 2π · δ_Q3(K) (достаточно!)
 2. Общий scale(c) лемма:
   - Сделать rescaling абстрактным, потом специализация c=2π
   - Для ревьюера: "heat-RKHS invariant under affine scaling"
 3. Namespace isolation:
   - Использовать RKHS_Standalone.ξ vs Q3.xi_n
   - Или qualified imports

---
 AGENTIC RUN #1.5 (HOTFIX) - РКХС BRIDGE

 Один агент, критический fix:

 Исправить Q3/Proofs/RKHS_contraction_bridge.lean:
 1. Добавить qualified import standalone
 2. Заменить exact RKHS_contraction_axiom на rescaling bridge
 3. Проверить: #print axioms RKHS_contraction_Q3 должен быть CLEAN

---
 AGENTIC RUN #2 - ОСТАЛЬНЫЕ SORRY

 Agent 1: Q_Lipschitz sorry

 - Файл: Q3/Proofs/Q_Lipschitz.lean:165
 - Documented proof strategy уже есть
 - Использовать: a_star_bdd_on_compact, W_sum bounded, MeasureTheory

 Agent 2: Q_nonneg_bridge sorry (3 штуки)

 - Q3/Proofs/Q_nonneg_bridge.lean
 - :166 - Finset.sum_image (техническое)
 - :202 - matrix norm definitions match
 - :215 - sInf ↔ iInf conversion

 Agent 3: A1_density sorry (1 штука)

 - Q3/Proofs/A1_density.lean
 - :482 - Finset sum to Fin sum
 - :524 - AtomCone_K definition match

---
 AGENTIC RUN #3 - ИНТЕГРАЦИЯ

 - AxiomsTheorems.lean - интегрировать все bridges
 - MainTheorems.lean - создать RH_proven с чистыми аксиомами
 - Финальная верификация: #print axioms RH_proven

---
 ФАЙЛЫ ДЛЯ МОДИФИКАЦИИ

 Run #1.5 (HOTFIX):

 - Q3/Proofs/RKHS_contraction_bridge.lean - КРИТИЧНО: исправить axiom → standalone

 Run #2:

 - Q3/Proofs/Q_Lipschitz.lean:165 - закрыть sorry
 - Q3/Proofs/Q_nonneg_bridge.lean:166,202,215 - закрыть 3 sorry
 - Q3/Proofs/A1_density.lean: sum_atoms_in_cone → sorryAx (закрыть)

 Run #3:

 - Q3/AxiomsTheorems.lean - интегрировать bridges
 - Q3/MainTheorems.lean - RH_proven
 - Финальная верификация

---
 COORDINATE RESCALING REFERENCE

| Standalone (α)     | Q3 (ξ)             | Relation        |
| ------------------ | ------------------ | --------------- |
| α_n = log n        | ξ_n = log n/(2π)   | α = 2π·ξ        |
| nodes: log n ≤ K   | nodes:             | ξ_n             |
| t_α                | t_ξ                | t_α = (2π)²·t_ξ |
| δ_K (min dist)     | delta_K            | δ_α = 2π·δ_ξ    |
| heat exp(-gap²/4t) | heat exp(-gap²/4t) | INVARIANT!      |

---
 ТОНКИЕ МЕСТА (PERELMAN warnings)

 1. Индексация n ≥ 2 - paper явно пишет, аккуратно с n=0,1
 2. Окно [−K,K] - но ξ_n ≥ 0 для n≥2, так что |ξ_n|≤K ↔ ξ_n≤K
 3. Веса w_Q vs w_RKHS - не перепутать! evenization эквивалентность
 4. δK - достаточно неравенства δ_actual ≥ δ_def для контракции

---
 КРИТЕРИЙ УСПЕХА

 После всех runs:
 lake env lean -c "import Q3.MainTheorems; #print axioms Q3.MainTheorems.RH_proven"

 Должен показать:
 'Q3.MainTheorems.RH_proven' depends on axioms:
 [propext, Classical.choice, Quot.sound,
  Q3.Weil_criterion, Q3.explicit_formula,
  Q3.Szego_Bottcher_eigenvalue_bound, Q3.Schur_test, ...]

 БЕЗ Tier-2 аксиом:
 - ❌ A1_density_axiom
 - ❌ Q_Lipschitz_on_W_K
 - ❌ RKHS_contraction_axiom
 - ❌ Q_nonneg_pos_arch_term
 - ❌ Q_nonneg_Gram_bound
 - etc.

---
 CHECKLIST ДЛЯ РЕВЬЮЕРА

 - #print axioms RKHS_contraction_Q3 - только standard
 - #print axioms Q_Lipschitz_on_W_K_thm - только standard
 - #print axioms Q_nonneg_from_bridge - только standard
 - #print axioms RH_proven - только Tier-1 + standard
╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌╌
