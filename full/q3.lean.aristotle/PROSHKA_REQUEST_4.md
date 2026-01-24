# PROSHKA REQUEST v5: SingleScale closure pack (3 axioms)

---

## §0. Статус и цель

**Цель:** закрыть ровно 3 открытые single‑scale аксиомы (mainline) и связать их в единый мост
к положительности на атомах при `t = t_critical`.

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
