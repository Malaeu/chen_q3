# Декомпозиция RH_Q3.pdf для формализации в Lean

## Обзор публикации

**Название**: Operator Methods for the Weil Criterion: Q3  
**Автор**: Eugen Malamutmann, MD (University of Duisburg-Essen)  
**Дата**: January 17, 2026  
**Страниц**: 62  

**Главный результат**: Доказательство гипотезы Римана через критерий Вейля — позитивность квадратичной формы Q(Φ) ≥ 0 на конусе Вейля W.

---

## Структура доказательства

### Модульная цепочка: (T0) + (A1') + (A2) + (A3) + (RKHS)

```
┌─────────────────────────────────────────────────────────────────┐
│                    RIEMANN HYPOTHESIS                           │
│                      (Theorem 11.2)                             │
└─────────────────────────────────────────────────────────────────┘
                              ▲
                              │
┌─────────────────────────────────────────────────────────────────┐
│                 WEIL POSITIVITY ON W                            │
│                    (Theorem 11.4)                               │
│                Q(Φ) ≥ 0 for all Φ ∈ W                          │
└─────────────────────────────────────────────────────────────────┘
                              ▲
          ┌───────────────────┼───────────────────┐
          │                   │                   │
┌─────────┴─────────┐ ┌───────┴───────┐ ┌────────┴────────┐
│  A3: TOEPLITZ     │ │ A1': DENSITY  │ │ A2: CONTINUITY  │
│  (Theorem 8.35)   │ │ (Theorem 6.3) │ │ (Lemma 7.3)     │
│  λ_min ≥ c_*/4    │ │ Fejér×heat    │ │ Lipschitz on K  │
└─────────┬─────────┘ └───────────────┘ └─────────────────┘
          │
          ▼
┌─────────────────────────────────────────────────────────────────┐
│              ARCHIMEDEAN FLOOR + RKHS CAP                       │
│     Lemma 8.19: P_A(θ) ≥ c_* = 11/10                           │
│     Corollary 8.22: ||T_P|| ≤ ρ(1) < c_*/4                     │
└─────────────────────────────────────────────────────────────────┘
```

---

## Граф зависимостей

### Статистика

| Метрика | Значение |
|---------|----------|
| Всего узлов | 58 |
| Всего рёбер | 79 |
| Фаз формализации | 7 |
| Суммарный ERS | 4199.9 |
| Средний ERS | 72.4 |
| Максимальный ERS | 351.6 |
| Hard blockers | 9 |

### Распределение по секциям

| Секция | Описание | Узлов | Avg ERS | Max ERS |
|--------|----------|-------|---------|---------|
| §5 | Normalization (T0) | 3 | 10.0 | 11.5 |
| §6 | Density (A1') | 2 | 16.4 | 30.1 |
| §7 | Continuity (A2) | 4 | 11.6 | 14.1 |
| §8 | Toeplitz Bridge (A3) | 25 | 87.2 | 351.6 |
| §9 | RKHS Contraction | 14 | 33.0 | 96.1 |
| §10 | Prime Cancellation (D3) | 6 | 138.6 | 216.4 |
| §11 | Main Theorem | 4 | 154.4 | 291.6 |

**Вывод**: Секция 8 (Toeplitz Bridge) — самая сложная и критическая, содержит 25 узлов с максимальным ERS = 351.6.

---

## Критический путь

```
lemma_8_12 (Core contribution)
    │ ERS = 100.8
    ▼
lemma_8_14 (Archimedean floor)
    │ ERS = 132.5
    ▼
lemma_8_19 (Uniform Archimedean floor) ← КЛЮЧЕВАЯ ЛЕММА
    │ ERS = 223.8, c_* = 11/10
    ▼
thm_8_35 (Uniform A3 bridge) ← САМЫЙ ВЫСОКИЙ ERS
    │ ERS = 351.6, λ_min ≥ c_*/4
    ▼
thm_11_4 (Main positivity on W)
    │ ERS = 245.8, Q(Φ) ≥ 0
    ▼
thm_11_2 (Riemann Hypothesis)
    │ ERS = 76.7
    ▼
    RH ✓
```

**Суммарный ERS критического пути**: ~1130

---

## TOP-10 узлов по ERS (приоритет формализации)

| # | ID | ERS | Raw | Inherited | CPB | Type | Blocker |
|---|---|---|---|---|---|---|---|
| 1 | thm_8_35 | 351.6 | 144.0 | 207.6 | 0.0 | theorem | hard |
| 2 | thm_11_3 | 291.6 | 36.0 | 255.6 | 0.0 | theorem | soft |
| 3 | prop_8_4 | 288.2 | 30.0 | 258.2 | 0.0 | proposition | soft |
| 4 | thm_11_4 | 245.8 | 52.5 | 193.3 | 0.0 | theorem | hard |
| 5 | lemma_8_19 | 223.8 | 108.0 | 115.8 | 0.0 | lemma | hard |
| 6 | thm_10_6 | 216.4 | 52.5 | 163.9 | 0.0 | theorem | hard |
| 7 | lemma_10_1 | 166.5 | 90.0 | 76.5 | 0.0 | lemma | hard |
| 8 | cor_8_21 | 150.6 | 60.0 | 90.6 | 0.0 | corollary | soft |
| 9 | cor_8_22 | 134.7 | 60.0 | 74.7 | 0.0 | corollary | soft |
| 10 | lemma_8_14 | 132.5 | 60.0 | 60.5 | 12.0 | lemma | soft |

---

## Hard Blockers (9 узлов)

Эти узлы требуют особого внимания — они блокируют прогресс и имеют высокую сложность:

| ID | Name | ERS | Фаза |
|---|---|---|---|
| lemma_8_30 | Szegő-Böttcher discretisation | 108.0 | 1 |
| thm_9_6 | Strict contraction | 96.1 | 2 |
| lemma_8_19 | Uniform Archimedean floor | 223.8 | 3 |
| thm_8_35 | Uniform A3 bridge | 351.6 | 5 |
| lemma_10_1 | Dispersion via A2/A3 data | 166.5 | 5 |
| thm_11_4 | Main positivity on W | 245.8 | 6 |
| thm_10_6 | Structural prime cancellation | 216.4 | 6 |
| thm_10_2 | D3: Structural contraction | 126.9 | 6 |
| thm_10_9 | Amplitude gate without D3 | 122.8 | 6 |

---

## План формализации в Lean

### Фаза 1: Базовые леммы (20 узлов)

**Приоритет**: Начать с hard blockers без зависимостей

```lean
-- Высший приоритет в Фазе 1
lemma_8_30  -- Szegő-Böttcher discretisation (ERS=108, hard)
lemma_8_12  -- Core contribution (ERS=100.8, soft)
lemma_8_16  -- Digamma monotonicity (ERS=100.8, soft)
```

**Стратегия**: 
- `lemma_8_30` требует теорию Toeplitz-операторов из Mathlib
- `lemma_8_12` и `lemma_8_16` — аналитические оценки, использовать `norm_balancer.py`

### Фаза 2: Промежуточные результаты (14 узлов)

```lean
-- Высший приоритет в Фазе 2
lemma_8_14  -- Archimedean floor (ERS=132.5, soft)
thm_9_6     -- Strict contraction (ERS=96.1, hard)
```

**Стратегия**:
- `lemma_8_14` зависит от `lemma_8_12` и `lemma_8_13`
- `thm_9_6` — ключевая теорема RKHS, требует спектральную теорию

### Фаза 3: Ключевая лемма (6 узлов)

```lean
-- КРИТИЧЕСКИЙ УЗЕЛ
lemma_8_19  -- Uniform Archimedean floor (ERS=223.8, hard)
            -- Устанавливает c_* = 11/10
```

**Стратегия**:
- Это "бутылочное горлышко" всего доказательства
- Требует точные численные оценки для a(1/2), a(3/2), a(5/2)
- Использовать `norm_balancer.py` для верификации неравенств

### Фаза 4: Следствия (5 узлов)

```lean
cor_8_21  -- Uniform discretisation threshold (ERS=150.6)
cor_8_22  -- Uniform prime cap time (ERS=134.7)
```

### Фаза 5: Главная теорема A3 (5 узлов)

```lean
-- САМЫЙ ВЫСОКИЙ ERS
thm_8_35  -- Uniform A3 bridge (ERS=351.6, hard)
          -- λ_min(T_M[P_A] - T_P) ≥ c_*/4 > 0
```

**Стратегия**:
- Собирает все предыдущие результаты
- Требует тщательной проверки всех констант

### Фаза 6: Финальные теоремы (5 узлов)

```lean
thm_11_4  -- Main positivity on W (ERS=245.8, hard)
          -- Q(Φ) ≥ 0 for all Φ ∈ W
```

### Фаза 7: Гипотеза Римана (3 узла)

```lean
thm_11_2  -- Riemann Hypothesis (ERS=76.7)
          -- (T0)+(A1')+(A2)+(A3)+(RKHS) ⟹ RH
```

---

## Критические константы

| Константа | Значение | Источник | Используется в |
|-----------|----------|----------|----------------|
| t_sym | 3/50 = 0.06 | Lemma 8.19 | A3 bridge |
| B_min | 3 | Lemma 8.19 | A3 bridge |
| c_* | 11/10 = 1.1 | Lemma 8.19 | Archimedean floor |
| M_0^unif | ⌈C_SB L_*/c_*⌉ | Corollary 8.21 | Discretisation |
| t^unif_*,rkhs | 1 | Corollary 8.22 | RKHS cap |
| w_max | 2/e ≈ 0.7358 | Lemma 9.8 | Weight bound |
| C_SB | 4 | Lemma 8.30 | Szegő-Böttcher |

---

## Рекомендации по применению Aristotle-эмулятора

### 1. Использовать `norm_balancer.py` для:
- Lemma 8.12 (Core contribution) — неравенство с exp и интегралами
- Lemma 8.18 (Sample-point bounds) — точные значения a(1/2), a(3/2), a(5/2)
- Lemma 8.19 (Archimedean floor) — P_A(θ) ≥ 11/10

### 2. Использовать `effective_risk.py` для:
- Приоритизации работы над hard blockers
- Отслеживания прогресса по фазам
- Выявления узких мест

### 3. Использовать `sorry_system_analyzer.py` для:
- Построения скелета доказательства с sorry
- Итеративного заполнения sorry

### 4. Тактики Lean для каждого типа:

| Тип леммы | Рекомендуемые тактики |
|-----------|----------------------|
| Аналитические оценки | `nlinarith`, `positivity`, `norm_num` |
| Интегралы | `MeasureTheory.integral_*`, `intervalIntegral.*` |
| Спектральные | `Matrix.eigenvalue_*`, `LinearMap.*` |
| Топологические | `IsCompact.*`, `Continuous.*` |

---

## Файлы проекта

```
rh_q3_analysis/
├── extracted_structure.md      # Извлечённая структура публикации
├── build_dependency_graph.py   # Скрипт построения графа
├── visualize_graph.py          # Скрипт визуализации
├── dependency_graph.json       # Граф в JSON формате
├── ers_analysis.png            # Визуализация ERS
├── dependency_graph.png        # Визуализация графа
├── formalization_plan.md       # План формализации по фазам
└── RH_Q3_DECOMPOSITION_REPORT.md  # Этот отчёт
```

---

## Заключение

Публикация RH_Q3.pdf декомпозирована на **58 узлов** (теоремы, леммы, следствия) с **79 зависимостями**. 

**Ключевые выводы**:

1. **Критический путь** проходит через секцию 8 (Toeplitz Bridge), где находится узел с максимальным ERS = 351.6 (`thm_8_35`)

2. **9 hard blockers** требуют особого внимания, особенно `lemma_8_19` (Archimedean floor) — это "бутылочное горлышко" всего доказательства

3. **Секция 8** содержит 43% всех узлов и 52% суммарного ERS — это основная область работы

4. **Формализация в 7 фаз** позволяет параллелизировать работу внутри каждой фазы

5. **Численный анализ** (`norm_balancer.py`) критически важен для лемм с точными константами (c_* = 11/10)

---

*Сгенерировано Aristotle-эмулятором v7*
