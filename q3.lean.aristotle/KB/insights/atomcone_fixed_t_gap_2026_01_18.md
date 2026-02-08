---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Insight: AtomCone_K_fixed — обнаруженный gap

**Date:** 2026-01-18
**Status:** CRITICAL — блокирует Q_nonneg closure
**Discovery:** mgrep semantic search по базе знаний

---

## Симптом (текущая сессия)

`Q3/Proofs/Q_nonneg_bridge.lean` не компилируется:
```
error: type mismatch
  htau i : |τ i| + B i ≤ K
  expected: |τ i| ≤ K
```

---

## Root Cause Analysis (из базы)

### Проблема #1: Support mismatch (РЕШЕНА)
- **Было:** `τ ∈ [-K,K], B ≤ K` → support ⊆ [-2K, 2K]
- **Нужно:** support ⊆ [-K, K]
- **Решение:** Изменить условие на `|τ| + B ≤ K`
- **Статус:** ✅ Реализовано в `AtomCone_K`

### Проблема #2: Quantifier mismatch (НЕ РЕШЕНА)
- **AtomCone_K:** квантифицирует `∀ t > 0` (произвольный t для каждого атома)
- **A3/RKHS bounds:** доказаны для ФИКСИРОВАННЫХ параметров:
  - A3 floor: `t_sym = 3/50 = 0.06`
  - RKHS cap: `t_rkhs_cap = 40`
- **Результат:** Гипотезы аксиомы не покрывают заключение
- **Статус:** ❌ Обсуждено, НЕ реализовано

---

## Решение (из Прошка-сессии 2026-01-16)

### AtomCone_K_fixed

```lean
def AtomCone_K_fixed (K t₀ : ℝ) : Set (ℝ → ℝ) :=
  { g | ∃ (n : ℕ) (c B τ : Fin n → ℝ),
        (∀ i, c i ≥ 0) ∧
        (∀ i, B i > 0) ∧
        (∀ i, |τ i| + B i ≤ K) ∧
        (∀ x, g x = ∑ i, c i * Fejer_heat_atom (B i) t₀ (τ i) x) ∧
        g ∈ W_K K }
```

### Ключевые свойства
1. `AtomCone_K_fixed K t₀ ⊆ AtomCone_K K` (subset)
2. Density сохраняется (Lemma 6.4 в RH_Q3.pdf)
3. Bounds теперь совпадают: фиксированный t₀ = t_sym или t_rkhs

---

## Связь параметров (из базы)

Два разных heat kernel:
- `heat_kernel_A1`: `exp(-x²/(4t))`
- `fejer_heat_window`: `exp(-4π²t'ξ²)`

Преобразование: **t' = 1/(16π²t)**

| heat_kernel_A1 (t) | fejer_heat_window (t') |
|--------------------|------------------------|
| t = 0.06           | t' ≈ 0.105             |
| t = 40             | t' ≈ 0.000158          |

---

## Action Items

1. [ ] Добавить `AtomCone_K_fixed` в `Q3/Axioms.lean`
2. [ ] Добавить лемму `AtomCone_K_fixed_subset : AtomCone_K_fixed K t₀ ⊆ AtomCone_K K`
3. [ ] Переписать `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` для fixed cone
4. [ ] Обновить `Q_nonneg_bridge.lean` под новые типы
5. [ ] Проверить что density A1 работает с fixed t₀

---

## Sources

- `docs/Proof_RH_Dezember_25/2026-1-16 20-31-3-Rayleigh_Q_identification_debug.txt`
- `docs/Proof_RH_Dezember_25/2026-1-13 22-34-58-Proshka_Briefing_A1.txt`
- `PROJECT_ORCHESTRATOR.md` (A1_density Definitional Issue section)

---

*Discovered via mgrep semantic search on project knowledge base*
