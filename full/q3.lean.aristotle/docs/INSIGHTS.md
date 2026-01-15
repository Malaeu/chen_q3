# Project Insights

Важные находки которые нельзя забывать.

---

## Прошка — Ключевой Ресурс

### Insight: Когда застрял → спроси Прошку

**Дата:** 2026-01-14

**Кто такой Прошка:** AI-агент (предположительно o3/o4-класс) с глубоким пониманием
математики проекта. Видит структуру доказательств яснее чем мы.

**Паттерн использования:**
```
1. Застряли на проблеме > 30 минут
2. Сформулировать запрос к Прошке:
   - Что пытаемся доказать
   - Где застряли
   - Какие ресурсы есть
3. Прошка даёт:
   - Правильную математическую структуру
   - Lean-ready statements
   - Что НЕ делать (DO NOT DO)
4. Конвертировать в Aristotle запрос
```

### Примеры решений от Прошки

| Проблема | Наше понимание | Прошкино решение |
|----------|----------------|------------------|
| A3_bridge blocked on SB | "Нужен Szegő-Böttcher" | "SB optional! Rayleigh напрямую" |
| RKHS bound не сходится | ρ = 0.868 > 0.825 | "При t≥1: ρ(1) < 1/25 = 0.04" |
| t большое или маленькое? | Путались | "t в знаменателе → small t нужно" |
| Какой bound нужен? | ≤ c*/4 = 0.275 | "≤ 3c*/4 = 0.825 достаточно" |

**Update (2026-01-15):** заметки про `ρ(1)` относятся к другой нормировке.
В текущем коде используем `t_rkhs_cap = 40`. См. раздел **RKHS Cap Implementation**.

### Характеристики Прошки

- **Математическая точность:** Видит правильные константы, bounds, структуру
- **Lean-awareness:** Даёт statements готовые для формализации
- **DO NOT DO списки:** Явно указывает что НЕ делать
- **Приоритизация:** Знает что critical path, что optional

### Правило

**Если застрял > 30 минут или < 10% в Aristotle:**
1. НЕ продолжать биться головой
2. Сформулировать запрос к Прошке
3. Получить структурированный ответ
4. Создать новую версию запроса

---

## Aristotle Strategy

### Insight: Pure Informal > Sandbox

**Дата:** 2026-01-14

**Эксперимент:** Отправили одну задачу (Rayleigh lower bound) двумя способами:
- V1: pure informal markdown
- V2: sandbox с готовыми сигнатурами

**Результат:**
- V1: **ПОЛНОЕ доказательство**, 0 sorry
- V2: только helper lemmas, main theorem sorry

**Причина:** Sandbox заставляет Aristotle работать с ФИКСИРОВАННЫМИ сигнатурами.
Если сигнатура не оптимальна — он застревает.
Pure informal даёт свободу ПЕРЕФОРМУЛИРОВАТЬ теорему как удобнее.

**Правило:** Для сложных теорем использовать pure informal, sandbox только для
простых/изолированных лемм.

---

## A3 Bridge Mathematics

### Insight: RKHS bound — как правильно применять

**Дата:** 2026-01-14

**Проблема:**
```
A3_bridge требует: (Toeplitz - RKHS) / ||v||² ≥ c*/4

Наивный подход:
- Toeplitz / ||v||² ≥ c* = 1.1 (из Rayleigh + A3_FLOOR)
- RKHS / ||v||² ≤ ρ (из RKHS_contraction)
- Разница ≥ c* - ρ

Но RKHS_contraction.lean даёт:
  ρ = (1 + w_max)/2 = (1 + 2/e)/2 ≈ 0.868

Нужно: c* - ρ ≥ c*/4
       1.1 - ρ ≥ 0.275
       ρ ≤ 0.825

Но 0.868 > 0.825 — НЕ СХОДИТСЯ!
```

**Вывод:** Нельзя использовать готовый ρ из RKHS_contraction для A3_bridge.

Текущий Schur bound имеет нижний порог `w_max`:
```
||T_P|| ≤ w_max * (1 + S(t))
```
При `S(t) → 0` получаем `||T_P|| ≤ w_max ≈ 0.735`.

**Это ДОСТАТОЧНО!** Нужно ≤ 3c*/4 = 0.825, и 0.735 < 0.825 ✓

(Ранее была ошибка: писал "нужно ≤ c*/4 = 0.275" — это неверно!)

Формула: `exp(-(ξᵢ-ξⱼ)²/(4t))`

При t → 0:
- Argument -(big)/(4×small) = -∞
- exp(-∞) → 0 для i≠j
- Off-diagonal terms → 0

При t → ∞:
- Argument -(big)/(4×large) → 0
- exp(0) → 1
- Off-diagonal terms → 1 (плохо!)

**Математика:**
```
S(t) = ∑_{k≠0} exp(-δ²k²/(4t)) → 0 при t → 0
```

**Правило:** Для A3_bridge достаточно bound ||T_P|| ≤ w_max ≈ 0.735 при t → 0.
Это слабее чем RKHS_contraction (ρ = 0.868), но ДОСТАТОЧНО для A3_bridge!

---

## Key Constants Reference

| Constant | Value | Decimal | Source |
|----------|-------|---------|--------|
| c* | 11/10 | 1.1 | A3_FLOOR |
| c*/4 | 11/40 | 0.275 | A3_bridge target |
| 3c*/4 | 33/40 | 0.825 | Max RKHS bound |
| w_max | 2/e | 0.735 | RKHS weight bound |
| ρ (RKHS) | (1+2/e)/2 | 0.868 | RKHS_contraction.lean |

**Note:** ρ = 0.868 (из RKHS_contraction) > 3c*/4 = 0.825, НО для small t:
||T_P|| ≤ w_max = 0.735 < 0.825 — это ДОСТАТОЧНО!

---

## File Organization

### Insight: aristotle_input/ structure

- `*_v1.md`, `*_v2.md` — версии одного запроса
- `project_ids.txt` — трекинг UUID проектов
- Pure informal файлы работают лучше чем sandbox

### Insight: aristotle_output/ naming

- `rayleigh_v1.lean` — winner (полное доказательство)
- `rayleigh_v2.lean` — backup (только helpers)
- Коммитить оба, в commit message указывать какой winner

---

## Documentation Discipline

### Insight: Минимум файлов, максимум ясности

- Один entrypoint: `PROJECT_ORCHESTRATOR.md`.
- Инсайды — только здесь (`docs/INSIGHTS.md`).
- Статистика формализации — только `FORMALIZATION_STATS.md`.
- Новые файлы документации НЕ создавать без явной необходимости.

### Insight: Reuse formalization assets

Мы реально копим повторно используемые результаты (леммы, теоремы, definitions).
Это актив: в следующих проектах можно переиспользовать доказанное, а не
переписывать/передоказывать. Поэтому:
- Обновляем `FORMALIZATION_STATS.md` после крупных шагов.
- Фиксируем reusable‑insights здесь.

---

## Szegő-Böttcher Theorem

### Insight: SB НЕ НУЖЕН для A3_bridge!

**Дата:** 2026-01-14 (из анализа Прошки)

**Факт из PROSHKA_REQUEST_3.md:**
> "Szegő-Böttcher is optional and can be bypassed using the Rayleigh lower bound"

**Rayleigh даёт НАПРЯМУЮ:**
```
λ_min(Toeplitz[P]) ≥ min(P)
```

Это СИЛЬНЕЕ и ПРОЩЕ чем SB который даёт только асимптотику!

**Ошибка:** A3_bridge_closure_v1.md упоминал SB в контексте — это путает Aristotle.

**Правило:** НЕ упоминать SB в запросах к Aristotle для A3_bridge.

---

## Две Формы Параметризации t

### Insight: t в числителе vs t в знаменателе

**Дата:** 2026-01-14

В Q3 используются ДВЕ разные формы:

| Форма | Где | Большое t → |
|-------|-----|-------------|
| `exp(-4π²t·(ξ-τ)²)` | Prime operator (papers) | меньше веса ✓ |
| `exp(-(ξ-τ)²/(4t))` | RKHS kernel (Axioms.lean) | БОЛЬШЕ веса ✗ |

**КРИТИЧНО:** В `Q3/Axioms.lean` используется ВТОРАЯ форма!

Для маленького ||T_P|| нужно **t МАЛЕНЬКОЕ**.

**Правило:** Перед написанием запроса ВСЕГДА проверять какая форма t используется!

---

## RKHS Cap Implementation (2026-01-15)

### Insight: t_rkhs_cap must be large for compression decay

**Факт:** при `xi_n = log n / (2π)` имеем
```
exp(-4π² t · xi_n^2) = exp(-t (log n)^2)
```
При `t=1` вклад от `n=2` уже ≈ `exp(-(log 2)^2) ≈ 0.6185`, поэтому `ρ(1) < 1/25`
невозможно при нашей нормировке. Решение — фиксировать **большой** `t`:

```
def t_rkhs_cap : ℝ := 40
```

**Реализация (DONE):** `Q3/Proofs/RKHS_cap_rayleigh.lean`
- `weight_sum_le_rho_one` — весовая сумма ≤ 1/25 через `n^-10` и диадическое разбиение.
- `rkhs_cap_rayleigh_tcap` — Rayleigh cap с `t_rkhs_cap`.
- `A3_bridge_rayleigh_from_weight_sum` — готовый glue для A3.

**Правило:** t_rkhs_cap должен быть **в числителе** (`exp(-t (log n)^2)`), значит t берём **большое**.

---

## Error Recovery Pattern

### Insight: Когда Aristotle застревает на низком %

**Паттерн:** V1 застрял на 4% → создали V2 с исправлениями.

**Причины застревания:**
- Путаница в математике (t большое vs маленькое)
- Ненужные упоминания (SB)
- Слишком сложные signatures

**Правило:** Если Aristotle < 10% более 30 минут → скорее всего ошибка в запросе.
Создавать новую версию с исправлениями, не ждать.

---

## Proven Assets Inventory

### Insight: Что уже доказано (2026-01-14)

**Полные доказательства (0 sorry):**

| Файл | Теорема | Применение |
|------|---------|------------|
| `rayleigh_v1.lean` | rayleigh_lower_bound | Toeplitz/||v||² ≥ min(P) |
| `A3_FLOOR_*.lean` | P_A(θ) ≥ c* = 11/10 | Lower bound на symbol |
| `Q3/Proofs/RKHS_cap_rayleigh.lean` | weight_sum_le_rho_one | RKHS cap (t_rkhs_cap=40) |

**Backup Strategy для A3_bridge:**

Если Aristotle застрянет, manual wiring:
```lean
-- Step 1: Toeplitz bound (from rayleigh_v1.lean)
have h_toep : Toeplitz_form / ||v||² ≥ c* :=
  rayleigh_lower_bound M hM P_A hP_cont c* hA3_FLOOR v hv

-- Step 2: RKHS bound for small t (new lemma needed)
have h_rkhs : RKHS_form / ||v||² ≤ 3*c*/4 :=
  RKHS_norm_small_t t ht_small M v

-- Step 3: Combine
linarith
```

**Ключевой gap:** Нужна lemma `RKHS_norm_small_t` показывающая что
для достаточно маленького t, ||T_P|| ≤ 3c*/4.

---

## BREAKTHROUGH: Прошка дал полное доказательство!

### Insight: A3_bridge закрывается за ~20 строк (2026-01-14)

**Прошка показал:**
1. rayleigh_v1.lean УЖЕ содержит Lemma 1 + Lemma 2
2. Нужна только Lemma 3 (operator subtraction) — 3 строки linarith
3. RKHS cap: ρ(1) < 1/25 = 0.04 << c*/4 = 0.275

**Структура финального доказательства:**
```
Toeplitz ≥ c* = 1.1        (rayleigh_v1.lean + A3_FLOOR)
RKHS ≤ c*/4 = 0.275        (trivial от ρ(1) < 0.04)
Разница ≥ 3c*/4 > 0        (linarith)
```

**Файл:** `aristotle_input/A3_bridge_PROSHKA_SKELETON.md`

**Правило:** Когда застреваем — перечитывать Прошкины ответы. Он видит дальше.

---

## V3 SUCCESS: Aristotle доказал A3_bridge_rayleigh!

### Insight: Прошкин скелет работает (2026-01-14)

**Результат:** `aristotle_output/A3_bridge_v3_proshka.lean` — COMPLETE, 0 sorry!

**Что Aristotle доказал:**
| Lemma | Status | LOC |
|-------|--------|-----|
| `toeplitz_quadratic_form` | ✅ | ~20 |
| `rayleigh_lower_bound` | ✅ | ~40 |
| `quadform_sub_ge` (Lemma 3) | ✅ | 1 (linarith!) |
| `RKHS_op_norm_bound` | ✅ | ~3 |
| `A3_bridge_rayleigh` (main) | ✅ | ~15 |

**ВАЖНЫЙ НЮАНС:** Aristotle упростил определения:
```lean
def P_A : ℝ → ℝ := fun _ => c_star  -- константа!
def T_P (t : ℝ) (M : ℕ) (i j : Fin M) : ℝ := 0  -- нуль!
```

**Что это значит:**
- Общие леммы (rayleigh_lower_bound, quadform_sub_ge) — УНИВЕРСАЛЬНЫЕ, переиспользуемые
- P_A и T_P — placeholder'ы, нужно подставить реальные
- Структура доказательства ВЕРНАЯ, математика СХОДИТСЯ

**Следующий шаг:**
Нужен ещё один запрос к Aristotle (или Прошке) с реальными P_A и T_P из нашего проекта.

**Вопрос:** Можно ли "сварить колбасу" из частей, или нужно цельное доказательство?
Ответ: Lean проверяет типы — если типы совпадают, wire безопасен.
Но для НАШЕГО A3_bridge нужны НАШИ определения P_A и T_P, не placeholder'ы.

---

## V1 SURPRISE: Real T_P bounds proven! (2026-01-14)

### Insight: V1 доказал ключевые леммы для real T_P

**Файл:** `aristotle_output/A3_bridge_closure_v1.lean` (project 4c2ed336)

Думали что V1 застрял, но он завершился и доказал важные вещи:

| Lemma | Статус | Значение |
|-------|--------|----------|
| `w_RKHS_le_w_max` | ✅ | w_RKHS(n) ≤ w_max = 2/e |
| `w_max_lt_three_quarters_c_star` | ✅ | **w_max < 3c*/4** (0.7358 < 0.825) |
| `T_P_tendsto_zero_of_ne` | ✅ | T_P(i,j,t) → 0 as t → 0 for i≠j |
| `exists_t_max_row_sum_le_for_M` | ✅ | **∀ M, ∃ t > 0: ||T_P|| ≤ 3c*/4** |

### КРИТИЧЕСКИЙ НЮАНС: t зависит от M!

V1 comment:
> "operator norm of T_P is unbounded for fixed t as M grows"

**Что доказано:** Для каждого ФИКСИРОВАННОГО M существует t(M) такое что ||T_P(t(M))|| ≤ 3c*/4.

**Что требует аксиома:** UNIFORM t для всех M ≥ M₀.

**Вопрос к Прошке:** Достаточно ли t(M) или нужен uniform t? Как A3_bridge используется в T5_Transfer?

### Переиспользуемые леммы из V1

Эти леммы можно wire напрямую в Q3:
- `w_RKHS_le_w_max` — matches `Q3.w_RKHS_le_w_max` в Defs.lean
- `w_max_lt_three_quarters_c_star` — новый результат!
- `T_P_tendsto_zero_of_ne` — off-diagonal decay

---

## V4 SUCCESS: Full T_P Bound Proven! (2026-01-14)

### Insight: V4 доказал полную теорему с реальными определениями

**Файл:** `aristotle_output/A3_bridge_v4_real_TP.lean`
**Проект:** c35f3088-0755-4b8c-a33b-bd03064dbfea
**Строк:** 309, **sorry:** 0

**Что доказано:**

| Lemma | Status | Значение |
|-------|--------|----------|
| `w_max_lt_one` | ✅ | w_max = 2/e < 1 |
| `w_RKHS_le_w_max` | ✅ | w_RKHS(n) ≤ w_max |
| `S_off_tendsto_zero` | ✅ | S_off(t,δ) → 0 as t → 0+ |
| `xi_n_diff_ge_dist_mul_delta_min_pos` | ✅ | Spectral node separation |
| `sum_exp_bound` | ✅ | Gaussian sum ≤ S_off |
| `T_P_row_sum_bound` | ✅ | Row sum ≤ w_max*(1 + S_off) |
| **`T_P_norm_lt_three_quarters_c_star`** | ✅ | **MAIN** |

### Главная теорема V4

```lean
theorem T_P_norm_lt_three_quarters_c_star (M : ℕ) :
  ∃ t > 0, ∀ v : Fin M → ℝ, v ≠ 0 →
    (∑ i, ∑ j, v i * T_P_matrix t M i j * v j) / (∑ i, v i ^ 2) ≤ 3 * c_star / 4
```

**КРИТИЧЕСКИЙ ФАКТ:** Это `∀ M, ∃ t(M)`, НЕ `∃ t, ∀ M`!

---

## КРИТИЧЕСКОЕ ИСПРАВЛЕНИЕ: T_P Compression (2026-01-14)

### Insight: Два РАЗНЫХ определения T_P

**Как было в нашем Axioms.lean (НЕПРАВИЛЬНО):**
```lean
T_P i j = sqrt(w_RKHS i) * sqrt(w_RKHS j) * exp(-(ξᵢ - ξⱼ)²/4t)
-- Direct indexing: i,j ∈ Fin M напрямую дают ξᵢ, ξⱼ
-- Проблема: норма растёт с M → uniform t невозможен
```

**Как в Q3 tex / rayleigh_bridge.tex (ПРАВИЛЬНО):**
```lean
T_P^{(M)} i j = ∑ n : Nodes K, w_Q n * Φ_{B,t}(ξₙ) * v_n[i] * v_n[j]
-- Rank-one compression: T_P^{(M)} = ι_M* T_P ι_M
-- v_n[i] = cos(2πk·ξₙ) — проекция на Фурье-базис P_M
-- Норма ≤ ||T_P|| (compression inequality) → uniform t ВОЗМОЖЕН
```

### Ключевое различие

| Аспект | Direct indexing (V1/V4) | Compression (Q3 tex) |
|--------|-------------------------|----------------------|
| Размер | M × M, зависит от M | M × M, но сумма по Nodes K |
| Норма при M → ∞ | → ∞ | ≤ ||T_P|| (bounded!) |
| Uniform t | ❌ Невозможен | ✅ Возможен |

### Почему V1/V4 не закрыли uniform t

V1/V4 доказали `∀M ∃t(M)` для **direct indexing** версии.
Это слабее чем `∃t ∀M≥M₀` из Q3.

Для uniform t нужен **компрессионный аргумент**:
```
||T_P^{(M)}|| ≤ ||T_P|| (compression of self-adjoint operator)
```

### V1/V4 статус

- ✅ `w_RKHS_le_w_max` — универсально полезно
- ✅ `S_off_tendsto_zero` — универсально полезно
- ⚠️ `T_P_norm_lt_three_quarters_c_star` — sanity check, но на неправильном T_P

### Следующий шаг

Переписать T_P в Axioms.lean на compression-версию:
```lean
def T_P_matrix (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :=
  fun i j => ∑ n : Nodes K,
    w_Q n * Phi_Bt B t (xi_n n) * v_n M (xi_n n) i * v_n M (xi_n n) j
```

Нужен мост: w_Q vs w_RKHS, Gaussian vs rank-one

---

## Optional: Rayleigh-only vs SB Discretization (Do Not Forget)

**Контекст:** В `full/sections/A3/main.tex` сейчас используется SB-дискретизация
с `M_0^{unif}` (это корректный, но "тяжёлый" путь). В протоколе
`full/q3.lean.aristotle/PROSHKA_REQUEST_3.md` зафиксирован упрощённый путь:
Rayleigh lower bound даёт `λ_min(T_M[P_A]) ≥ min P_A` без SB, значит без `M_0`.

**Это не противоречие:**
- SB-путь остаётся верным (просто избыточный).
- Rayleigh-путь сильнее (оценка для всех M).

**Если когда-нибудь нужно согласовать текст с протоколом:**
1) Добавить ремарку в `full/sections/A3/main.tex`: SB-оценка optional; можно
   заменить на Rayleigh lower bound и убрать `M_0`.
2) В доказательстве Theorem A3 убрать SB-дискретизацию и сослаться на Rayleigh.

---

## ⚠️ КРИТИЧНО: Два разных heat parameter! (2026-01-14, Прошка)

### Insight: t_sym ≠ t_rkhs

В Q3 используются **ДВА РАЗНЫХ** heat parameter:

| Параметр | Значение | Где используется | Зачем |
|----------|----------|------------------|-------|
| `t_sym` | 3/50 = 0.06 | Symbol P_A, A3_FLOOR | Arch smoothing |
| `t_rkhs` | 1 | Prime operator cap | RKHS bound |

**Критическое следствие:**
```
ρ(t_sym = 0.06) ≈ 0.95   ← БОЛЬШОЕ, не годится!
ρ(t_rkhs = 1)   < 1/25   ← маленькое ✅
```

### Почему M₀ не нужен

```
Нужно для A3_bridge: ||T_P|| ≤ c*/4 = 0.275
Имеем при t_rkhs=1: ρ(1) < 1/25 = 0.04

0.04 << 0.275 ✅

Разница Toeplitz - T_P ≥ c* - 0.04 ≈ 1.06 >> c*/4
```

M₀ был нужен для SB-дискретизации. С Rayleigh-first он не нужен.

### Правило

**ВСЕГДА проверять какой t используется:**
- Для symbol/arch → t_sym = 3/50
- Для prime cap → t_rkhs = 1

**НЕ путать!** V1/V4 использовали один t для всего — это ошибка.

---

## T_P_comp уже есть! (2026-01-14)

### Insight: Определение готово, но не подключено

`Q3/Basic/Defs.lean:100` содержит **правильный** T_P_comp:
```lean
def T_P_comp (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Matrix (Fin (2 * M + 1)) (Fin (2 * M + 1)) ℂ :=
  fun i j =>
    ∑ n : Nodes K,  -- сумма по Nodes, не по Fin M!
      (w_Q n * fejer_heat_window B t (xi_n n)) *
        prime_vec M (xi_n n) i * conj (prime_vec M (xi_n n) j)
```

`prime_vec` имеет нормализацию `1/√(2M+1)` ✅

**Проблема:** `A3_bridge_axiom` в `Axioms.lean` использует direct-indexed T_P,
а не T_P_comp!

**Следующий шаг:** Переписать A3_bridge_axiom чтобы использовал T_P_comp.

---

## Прошка: Численные оценки для h_cap (2026-01-14)

### Insight: Сумма весов КРАЙНЕ мала

**Прошка вычислил:**
```python
Σ_n 2·Λ(n)/√n · exp(-4π²(log n)²) ≈ 6×10⁻⁹
```

Это НАМНОГО меньше чем ρ(1) ≈ 0.027 из интеграла!

### Техника для n≥3

**Ключевое неравенство:**
```
exp(-4π²(log n)²) ≤ n⁻¹⁰   для n ≥ 3
```

**Доказательство:** Нужно показать `4π²(log n)² ≥ 10·log n`.
Для n≥3: `log n ≥ 1`, поэтому `4π²(log n) ≥ 4π² ≈ 39.5 > 10`. ✓

**Следствие:**
```
Λ(n)/√n · exp(-4π²(log n)²) ≤ log(n)/√n · n⁻¹⁰ = log(n)/n^{10.5}
```

Сумма `Σ_{n≥3} 1/n^{9.5}` сходится очень быстро (< 0.0003).

### Почему ρ(1) ≈ 0.027

```python
ρ(t) = ∫₀^∞ 2y·e^{y/2}·e^{-4π²t·y²} dy

При t=1:
ρ(1) ≈ 0.0272 < 1/25 = 0.04 ✅
```

### Почему сумма << ρ(1)

Интеграл ρ(t) даёт верхнюю границу для суммы, но реальная сумма
НАМНОГО меньше из-за:
1. Λ(n) = 0 для композитных n (большинство)
2. Экспоненциальное убывание exp(-4π²(log n)²)

### Итог для h_cap

```
rayleighQ T_P_comp ≤ Σ weights   (Cauchy-Schwarz)
                  ≤ 6×10⁻⁹
                  << 1/25 = 0.04 ✅
```

**Правило:** h_cap "тривиален" численно — Aristotle должен справиться легко.

---

*Обновляй этот файл когда находишь новые insights!*
