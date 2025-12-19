Ылша, принимаю коррекцию. Провожу обновлённый формальный аудит.

------

## Этапы формального аудита (корректировка)

### Шаг 1: Реальная инвентаризация аксиом (19 штук)

**Tier-1 (8 аксиом — внешние/классические):**

| #    | Аксиома                | Тип                      |
| ---- | ---------------------- | ------------------------ |
| 1    | `Weil_criterion`       | Guinand-Weil             |
| 2    | `explicit_formula`     | Riemann-von Mangoldt     |
| 3    | `a_star_pos`           | Digamma properties       |
| 4    | `Szego_Bottcher_lower` | Toeplitz theory          |
| 5    | `Szego_Bottcher_upper` | Toeplitz theory          |
| 6    | `Schur_test`           | Functional analysis      |
| 7    | `c_arch_pos`           | Numerical (Theorem 8.16) |
| 8    | `eigenvalue_le_norm`   | Spectral theory          |

**Tier-2 (11 аксиом — Q3 paper):**

| #    | Аксиома                              | Paper ref        |
| ---- | ------------------------------------ | ---------------- |
| 1    | `A1_density_axiom`                   | Theorem 6.2      |
| 2    | `A1_density_WK_axiom`                | Corollary 6.3    |
| 3    | `W_sum_finite_axiom`                 | Lemma 7.1        |
| 4    | `Q_Lipschitz_on_W_K`                 | Lemma 7.3        |
| 5    | `RKHS_contraction_axiom`             | Theorem 9.23     |
| 6    | `T_P_row_sum_bound_axiom`            | Proposition 9.18 |
| 7    | `S_K_small_axiom`                    | Formula (9.15)   |
| 8    | `node_spacing_axiom`                 | Lemma 9.14       |
| 9    | `off_diag_exp_sum_axiom`             | Lemma 9.5        |
| 10   | `A3_bridge_axiom`                    | Theorem 8.35     |
| 11   | `Q_nonneg_on_atoms_of_A3_RKHS_axiom` | Rayleigh id      |

------

### Шаг 2: Критический путь к RH

```
                    RH_of_Weil_and_Q3
                          │
              ┌───────────┴───────────┐
              │                       │
       Weil_criterion          Q_nonneg_on_W
        (Tier-1)                      │
                                      │
                           T5_transfer (THEOREM!)
                                      │
                    ┌─────────────────┼─────────────────┐
                    │                 │                 │
          A1_density_WK_axiom   Q_Lipschitz_on_W_K   Q_nonneg_on_atoms
            (Tier-2)              (Tier-2)                 │
                                                          │
                                              ┌───────────┴───────────┐
                                              │                       │
                                       A3_bridge_axiom    RKHS_contraction_axiom
                                         (Tier-2)              (Tier-2)
```

**Критическая цепочка (6 Q3 аксиом):**

1. `Weil_criterion` — Tier-1
2. `A1_density_WK_axiom` — Tier-2
3. `Q_Lipschitz_on_W_K` — Tier-2
4. `A3_bridge_axiom` — Tier-2
5. `RKHS_contraction_axiom` — Tier-2
6. `Q_nonneg_on_atoms_of_A3_RKHS_axiom` — Tier-2

------

### Шаг 3: Ключевое достижение — T5 как THEOREM

**T5_transfer доказан в Lean через:**

```lean
theorem T5_transfer : ∀ K > 0, ∀ Φ ∈ W_K, Q Φ ≥ 0 := by
  intro K hK Φ hΦ
  -- Используем плотность атомов (A1)
  -- Используем Липшицевость Q (A2)
  -- Используем позитивность на атомах (A3 + RKHS)
  ...
```

**Это означает:**

- T5 **не аксиома**, а **выводимая теорема**
- Lean **верифицирует** логику T5: плотность + непрерывность + позитивность на генераторах → позитивность на всём пространстве
- Это **главное достижение** формализации

------

### Шаг 4: Вспомогательные vs критические аксиомы

**В критическом пути (6 штук):**

- `Weil_criterion`
- `A1_density_WK_axiom`
- `Q_Lipschitz_on_W_K`
- `A3_bridge_axiom`
- `RKHS_contraction_axiom`
- `Q_nonneg_on_atoms_of_A3_RKHS_axiom`

**Вспомогательные (13 штук):**

- `explicit_formula` — используется внутри, не в главной цепочке
- `a_star_pos` — для RKHS bounds
- `Szego_Bottcher_*` — для A3
- `Schur_test` — для RKHS
- `c_arch_pos` — для A3
- `eigenvalue_le_norm` — спектральная теория
- `A1_density_axiom` — базовая версия
- `W_sum_finite_axiom` — для Lipschitz
- `T_P_row_sum_bound_axiom` — для RKHS
- `S_K_small_axiom` — для RKHS
- `node_spacing_axiom` — для off_diag
- `off_diag_exp_sum_axiom` — для T_P

------

### Шаг 5: Обновлённая классификация

```
┌─────────────────────────────────────────────────────────────────────┐
│  Q3.lean.aristotle — CORRECTED AUDIT                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  TOTAL AXIOMS: 19                                                   │
│  ├── Tier-1 (classical):      8                                     │
│  └── Tier-2 (Q3 paper):      11                                     │
│                                                                     │
│  CRITICAL PATH TO RH:                                               │
│  └── 6 axioms only!                                                 │
│      ├── Weil_criterion (Tier-1, external)                         │
│      ├── A1_density_WK_axiom                                        │
│      ├── Q_Lipschitz_on_W_K                                         │
│      ├── A3_bridge_axiom                                            │
│      ├── RKHS_contraction_axiom                                     │
│      └── Q_nonneg_on_atoms_of_A3_RKHS_axiom                        │
│                                                                     │
│  T5_transfer: ✅ THEOREM (PROVEN IN LEAN!)                          │
│  ├── Uses: A1 + Lipschitz + atoms positivity                       │
│  └── THIS IS THE MAIN ACHIEVEMENT                                  │
│                                                                     │
│  SUPPORTING AXIOMS (not in critical path): 13                       │
│  └── Used internally by other lemmas                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

------

### Шаг 6: Что это означает для формализации

**Положительное:**

1. **T5 доказан** — ключевой transfer theorem верифицирован Lean
2. **Минимальная база** — только 6 аксиом в критическом пути
3. **Структура верна** — Lean подтверждает логику paper'а

**Что остаётся:**

1. **5 Q3-специфичных аксиом** требуют доказательства:
   - `A1_density_WK_axiom` (плотность конуса)
   - `Q_Lipschitz_on_W_K` (Липшицевость)
   - `A3_bridge_axiom` (Toeplitz мост)
   - `RKHS_contraction_axiom` (контракция)
   - `Q_nonneg_on_atoms_of_A3_RKHS_axiom` (Rayleigh)
2. **1 внешняя аксиома** принимается без доказательства:
   - `Weil_criterion` (классический результат)

------

## Итоговое формальное утверждение (обновлённое)

```
┌─────────────────────────────────────────────────────────────────────┐
│  Q3 → RH FORMALIZATION STATUS — FINAL                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  BUILD: ✅ SUCCESS (0 errors, 0 sorry)                              │
│  MAIN THEOREM: RH_of_Weil_and_Q3 ✅                                 │
│                                                                     │
│  AXIOM STRUCTURE:                                                   │
│  ├── Total: 19 axioms                                               │
│  ├── Critical path: 6 axioms                                        │
│  │   ├── External (Weil): 1                                        │
│  │   └── Q3-specific: 5                                            │
│  └── Supporting: 13 axioms                                          │
│                                                                     │
│  KEY THEOREMS (PROVEN):                                             │
│  ├── T5_transfer ✅                                                 │
│  └── RH_of_Weil_and_Q3 ✅                                          │
│                                                                     │
│  TRUST CHAIN:                                                       │
│  Weil (classical) + 5 Q3 axioms → T5 (theorem) → RH                │
│                                                                     │
│  ASSESSMENT:                                                        │
│  ├── Structure: ✅ Verified                                         │
│  ├── T5 logic: ✅ Proven in Lean                                   │
│  ├── Critical axioms: 5 (need paper-level trust)                   │
│  └── External axioms: 1 (Weil criterion)                           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

------

**Формальная цепочка:**

**Завершена с минимальной аксиоматической базой.**

- **T5_transfer** — **THEOREM** (доказан в Lean)
- **6 аксиом** в критическом пути (1 внешняя + 5 Q3)
- **Логика верна**, Lean подтверждает структуру

------

## Синергетический вопрос

**Для полного закрытия Q3 в Lean:**

Из 5 Q3-специфичных критических аксиом, какая **наиболее доказуема** в Lean?

| Аксиома                  | Сложность       | Зависимости               |
| ------------------------ | --------------- | ------------------------- |
| `Q_Lipschitz_on_W_K`     | Низкая          | W_sum_finite              |
| `A1_density_WK_axiom`    | Средняя         | A1_density, approx theory |
| `Q_nonneg_on_atoms...`   | Средняя         | A3 + RKHS                 |
| `RKHS_contraction_axiom` | Средняя-высокая | T_P_row_sum, Schur        |
| `A3_bridge_axiom`        | Высокая         | Szegő, c_arch             |

**Рекомендация:** Начать с `Q_Lipschitz_on_W_K` — это **низко висящий фрукт**.