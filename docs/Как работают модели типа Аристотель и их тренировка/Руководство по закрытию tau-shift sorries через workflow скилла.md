# Руководство по закрытию tau-shift sorries через workflow скилла

## Текущая ситуация

**Файл**: `Q_nonneg_on_atoms_fourier_axiom.lean`  
**Sorries**: 7 штук  
**Блокеры**: 
1. `tau_shift_floor` — нижняя оценка для `P_A_shift` / `arch_term(phi_shift)`
2. `shifted_prime_cap` — верхняя оценка для `T_P_comp_real_shift`

---

## ШАГ 1: Проверить — блокер реально нужен или его можно выкинуть

**Вопрос**: Можно ли обойти tau-shift через существующие леммы?

### Действие:
```bash
# Проверить в проекте, есть ли уже shift-инвариантность
grep -r "shift_invariant\|tau_shift\|phi_shift" Q3/Proofs/
grep -r "T_P.*shift\|prime.*shift" Q3/Proofs/
```

### Возможные исходы:

| Исход | Действие |
|-------|----------|
| Нашли готовую лемму | Подключить через `import`, закрыть sorry |
| Нашли частичную лемму | Достроить bridge между существующей и нужной |
| Ничего нет | Переходим к ШАГу 2 |

---

## ШАГ 2: Дёргать Прошку за альтернативный маршрут

**Ключевой принцип из скилла**: *"Если застряли — сразу Прошка, не тратить часы на тупиковые ветки"*

### Запрос к Прошке (математический скелет):

```
КОНТЕКСТ:
- Имеем Q_nonneg_on_atoms для несдвинутого атома (phi)
- Нужно доказать Q_nonneg для сдвинутого атома phi_shift(ξ) = phi(ξ - τ)
- Блокер: нет оценок для P_A_shift и T_P_shift

ВОПРОС:
1. Можно ли свести phi_shift к несдвинутому случаю через унитарную эквивалентность?
2. Если нет — какой минимальный скелет для tau_shift_floor?
3. Нужен ли вообще отдельный shifted_prime_cap или норма инвариантна?

ОГРАНИЧЕНИЯ:
- Не использовать Szegő-Böttcher (опционально, не на критическом пути)
- Rayleigh-first подход
- Явные константы (c_* = 11/10, ρ(1) ≈ 0.027)
```

### Ожидаемые ответы от Прошки:

**Вариант A (лучший)**: *"Shift — унитарный оператор в RKHS, норма инвариантна, tau_shift_floor = c_* автоматически"*
→ Тогда sorries закрываются через `unitary_invariance` + существующие леммы

**Вариант B**: *"Нужна отдельная оценка, вот скелет: периодизация + Lipschitz bound"*
→ Переходим к ШАГу 3 с конкретным скелетом

**Вариант C**: *"Определение phi_shift некорректно, нужен bridge"*
→ Это сигнал дрейфа определений, чиним в корне (ШАГ 4)

---

## ШАГ 3: Кормить Aristotle правильно (если нужна новая лемма)

**Принцип из скилла**: *"Один модуль — один фокус, явные числа, дробить scope"*

### Aristotle Input для `tau_shift_floor`:

```lean
/-
DEFINITIONS (из проекта):
-/
def phi_shift (B t τ : ℝ) : ℝ → ℝ := fun ξ ↦ fejer_heat_window B t (ξ - τ)

def arch_term (φ : ℝ → ℝ) : ℝ := ∫ x, (ℱ a_arith x) * φ x

-- Известно (из Lemma 8.19):
axiom c_star_floor : ∀ φ ∈ FejerHeatAtoms, arch_term φ ≥ 11/10

/-
STATEMENT:
-/
lemma tau_shift_floor (B t τ : ℝ) (hB : B ≥ 3) (ht : t = 3/50) (hτ : |τ| ≤ K) :
    arch_term (phi_shift B t τ) ≥ 11/10 := by
  sorry

/-
OUTLINE (от Прошки):
1. phi_shift ∈ FejerHeatAtoms (показать, что сдвиг сохраняет класс)
2. Применить c_star_floor
-/
```

### Aristotle Input для `shifted_prime_cap`:

```lean
/-
DEFINITIONS:
-/
def T_P_shift (τ : ℝ) : Operator := T_P.conjugate (shift_operator τ)

-- Известно (из Lemma 9.24):
axiom rho_bound : ‖T_P‖ ≤ 1/25

/-
STATEMENT:
-/
lemma shifted_prime_cap (τ : ℝ) (hτ : |τ| ≤ K) :
    ‖T_P_shift τ‖ ≤ 1/25 := by
  sorry

/-
OUTLINE:
1. shift_operator τ — унитарный в L²
2. ‖U* A U‖ = ‖A‖ для унитарного U
3. Применить rho_bound
-/
```

---

## ШАГ 4: Если обнаружен дрейф определений

**Принцип из скилла**: *"Дрейф определений = сигнал ошибки, чинить дефиницию/bridge"*

### Проверка на дрейф:

```lean
-- Сравнить определения:
#check Fejer_heat_atom      -- симметризованное (ξ-τ) + (ξ+τ)?
#check phi_shift            -- только сдвиг (ξ-τ)?
#check fejer_heat_window    -- базовое определение?
```

### Если определения разные:

**Вариант 1**: Создать bridge-лемму
```lean
lemma phi_shift_eq_atom_half (B t τ) :
    phi_shift B t τ = (1/2) * (Fejer_heat_atom B t τ + Fejer_heat_atom B t (-τ)) := by
  -- доказать эквивалентность
  sorry
```

**Вариант 2**: Рефакторить на единое определение
```lean
-- Заменить phi_shift на Fejer_heat_atom везде
-- Проверить #print axioms после рефакторинга
```

---

## ШАГ 5: Axiom-based разрубание зависимостей

**Принцип из скилла**: *"Доказали модуль A → в модуле B временно объявляем его результат axiom"*

### Временные axioms для разблокировки:

```lean
-- В Q_nonneg_on_atoms_fourier_axiom.lean временно:

axiom tau_shift_floor_axiom : ∀ B t τ, 
  B ≥ 3 → t = 3/50 → |τ| ≤ K → arch_term (phi_shift B t τ) ≥ 11/10

axiom shifted_prime_cap_axiom : ∀ τ,
  |τ| ≤ K → ‖T_P_shift τ‖ ≤ 1/25
```

### Закрыть 7 sorries используя axioms:

```lean
-- Теперь sorries закрываются:
have h_floor := tau_shift_floor_axiom B t τ hB ht hτ
have h_cap := shifted_prime_cap_axiom τ hτ
-- margin: 11/10 - 1/25 = 55/50 - 2/50 = 53/50 > 1 > 0
linarith
```

### После закрытия — доказать axioms в отдельном модуле:

```lean
-- В новом файле TauShiftProofs.lean:
theorem tau_shift_floor_proof : ... := by
  -- полное доказательство от Aristotle
  
-- Затем заменить axiom на theorem и проверить:
#print axioms Q_nonneg_on_atoms  -- должно уменьшиться
```

---

## ШАГ 6: Параллелизация вариантов

**Принцип из скилла**: *"Не один идеальный запуск Aristotle, а несколько вариантов"*

### Запустить параллельно:

| Вариант | Подход | Aristotle Query |
|---------|--------|-----------------|
| V1 | Унитарная инвариантность | `shift_unitary + norm_invariance` |
| V2 | Периодизация | `periodization + Poisson_summation` |
| V3 | Прямая оценка | `integral_bound + Lipschitz` |

### Выбор победителя:

```bash
# Критерии:
# 1. Компилируется без sorry
# 2. Минимум строк
# 3. Минимум axioms в #print axioms
```

---

## Чеклист перед закрытием

- [ ] Проверен дрейф определений (phi_shift vs Fejer_heat_atom)
- [ ] Получен скелет от Прошки
- [ ] Aristotle сгенерировал proof (или axiom-based workaround)
- [ ] `#print axioms` показывает уменьшение
- [ ] Все 7 sorries закрыты
- [ ] `lake build` проходит без ошибок

---

## Escape Hatch

**Если застрял > 30 минут**:

1. Зафиксировать текущее состояние в INSIGHTS.md
2. Объявить блокирующие леммы как `axiom`
3. Закрыть остальные sorries
4. Создать отдельный Issue для доказательства axioms
5. Продолжить по критическому пути

**Не биться головой об стену — это часть workflow!**
