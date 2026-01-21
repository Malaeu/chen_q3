# Aristotle Proofs Database

## Цель
Каталогизировать все доказательства от Aristotle для:
1. Понимания какие леммы уже доказаны
2. Сравнения разных подходов к одной лемме
3. Выявления паттернов для оптимизации запросов

---

## Леммы по категориям

### Category A: Trigamma/Digamma Properties

| Лемма | Versions | Тактики | Статус |
|-------|----------|---------|--------|
| `im_trigamma_neg` | v3, v7, v8 | tsum analysis, Complex.im_tsum | ✅ 3 варианта |
| `im_trigamma_neg` | v12 | explicit summability + tsum_neg | ✅ NEW |
| `trigamma_summable` | v3 | comparison with 1/n² | ✅ |
| `trigamma_add_one` | v6, v7, v8 | index shift in tsum | ✅ 3 варианта |
| `trigamma_tendsto_zero` | v6, v7, v8 | dominated convergence | ✅ 3 варианта |
| `trigamma_tendsto_zero_complex` | v8 | squeeze theorem | ✅ NEW |

### Category B: Digamma Derivatives

| Лемма | Versions | Тактики | Статус |
|-------|----------|---------|--------|
| `digamma_add_one` | v3 | Gamma recurrence | ✅ |
| `deriv_digamma_add_one` | v8 | from diff_digamma_trigamma | ✅ NEW |
| `diff_digamma_trigamma_add_one` | v6, v7, v8 | recurrence + deriv | ✅ 3 варианта |
| `deriv_digamma_eq_trigamma` | - | NEEDED! | ❌ |

### Category C: Function a(ξ) Properties

| Лемма | Versions | Тактики | Статус |
|-------|----------|---------|--------|
| `deriv_a_eq` | v3, v7, v8 | chain rule + Complex.continuous_re | ✅ 3 варианта |
| `continuousOn_a` | v3, v7, v8 | AnalyticAt → ContinuousAt | ✅ 3 варианта |
| `deriv_a_pos` | v9 (conditional) | opaque defs, sign mismatch vs v3 | ⚠️ CONDITIONAL |
| `strictMonoOn_a` | v9 (conditional) | depends on deriv_a_pos + deriv_digamma_eq_trigamma | ⚠️ CONDITIONAL |
| `deriv_a_neg` | v11_fixed (local) | correct sign; depends on deriv_digamma_eq_trigamma | ⚠️ CONDITIONAL |
| `strictAntiOn_a` | v11_fixed (local) | correct sign; depends on deriv_digamma_eq_trigamma | ⚠️ CONDITIONAL |

### Category D: Auxiliary (v8 only)

| Лемма | Versions | Тактики | Статус |
|-------|----------|---------|--------|
| `diff_const` | v8 | induction on n | ✅ NEW |
| `digammaSeq` | v8 | definition | ✅ NEW |
| `digammaSeq_deriv` | v8 | HasDerivAt.sum | ✅ NEW |
| `digammaSeq_eq` | v8 | Finset.sum_range_succ' | ✅ NEW |
| `deriv_digammaSeq_tendsto_trigamma` | v8 | partial sums → tsum | ✅ NEW |

---

## Сравнение подходов

### im_trigamma_neg (3 версии)

**V3 (original):**
```lean
unfold trigamma
rw [Complex.im_tsum]
-- explicit formula for Im(1/(z+n)²)
-- summability via comparison
```

**V7 (repeat):**
```lean
have h_summable : Summable ...  -- сначала summability
have h_trigamma_pos : (trigamma z).im = tsum ...
have h_sum_neg : factorize -2*z.im
exact ... Summable.le_tsum
```

**V8 (refined):**
```lean
have h_series : (trigamma z).im = tsum Im(...)  -- через im_tsum
have h_im_term : ∀ n, explicit formula
rw [h_series, tsum_congr h_im_term]
refine' Summable.tsum_pos  -- НОВАЯ финальная тактика!
```

**Паттерн:** V8 использует `Summable.tsum_pos` вместо `Summable.le_tsum` — более прямой путь!

---

### deriv_a_eq (3 версии)

**V3/V7:**
```lean
convert HasDerivAt.deriv _ using 1
have h_chain : HasDerivAt (fun ξ => -Re(ψ(...))) ...
convert h_chain.const_add (log π) using 2
```

**V8:**
```lean
have h_deriv_def : HasDerivAt (fun ξ => log π - Re(ψ(...))) ...
exact h_deriv_def.deriv
```

**Паттерн:** V8 работает с полным выражением сразу, V3/V7 строят по частям.

---

## Выявленные паттерны

### Pattern 1: Tsum Tactics
- `Complex.im_tsum` — для Im(tsum) = tsum(Im)
- `tsum_congr` — для замены функции
- `Summable.tsum_pos` — для tsum > 0 когда все члены ≥ 0
- `Summable.le_tsum` — для нижних оценок

### Pattern 2: Analytic → Differentiable
```lean
have h_analytic : AnalyticAt ℂ f z := by
  apply DifferentiableOn.analyticAt
  ...
exact h_analytic.differentiableAt.hasDerivAt
```

### Pattern 3: Chain Rule for Real Part
```lean
have h_deriv : HasDerivAt (fun ξ => f(...)) derivative ξ := by
  -- compose with ofReal
rw [hasDerivAt_iff_tendsto_slope_zero]
convert Complex.continuous_re.continuousAt.tendsto.comp ...
```

### Pattern 4: Summability via Comparison
```lean
have h_bound : ∀ n, n ≥ 1 → ‖term n‖ ≤ 1/n^p := by
  ...
rw [← summable_nat_add_iff 1]
exact Summable.of_nonneg_of_le ... ... (Real.summable_one_div_nat_pow.2 ...)
```

---

## Рекомендации для запросов

1. **Указывать AXIOMS явно** — чтобы Aristotle не пере-доказывал
2. **Давать конкретные тактики** — если знаем какой подход работает
3. **Разбивать на мелкие шаги** — одна лемма за раз
4. **Использовать паттерны из DB** — копировать работающие подходы

---

## Файлы по версиям

| Version | File | Size | Lemmas |
|---------|------|------|--------|
| v3 | A3_FLOOR_v3_trigamma_foundations.lean | 10.9KB | 5 |
| v6 | A3_FLOOR_v6_deriv_foundations.lean | 23KB | 5+ |
| v7 | A3_FLOOR_v7_repeat.lean | 16KB | 6 (repeats) |
| v8 | A3_FLOOR_v8_monotonicity.lean | ~15KB | 12 (6 new!) |
| v11 | A3_FLOOR_v11_fixed.lean | local | monotonicity (correct sign, axioms) |
| v12 | 4ec30af1_aristotle.lean | Aristotle output | trigamma neg (clean) |

---

**Последнее обновление:** 2025-12-28
