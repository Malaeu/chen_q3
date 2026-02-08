---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Reverse Engineering Checklist: A3 Symbol Mismatch (2026-01-15)

Цель: быстро найти источник рассогласования между символами `a_star` и `P_A`.

### Быстрые индикаторы
- `c_star` приходит из A3_FLOOR (символ `P_A`), но A3-цепочка использует `ToeplitzMatrix ... a_star`.
- В `Q3/Axioms.lean` есть аксиоматический мост `c_star_le_c_arch`, который может скрывать рассогласование.

### Файлы, которые вскрывают проблему
- `Q3/Axioms.lean` — `Toeplitz_Rayleigh_lower_bound_uniform` (комментарий про `P=a_star, c=c_star`) + `c_star_le_c_arch`.
- `Q3/Proofs/A3_Bridge_Uniform.lean` — A3_FLOOR (`P_A_ge_c_star`) в тексте, но вывод через `A3_bridge_uniform` (с `a_star`).
- `Q3/Proofs/A3_bridge_rayleigh_first.lean` — гипотеза `RayleighQuotient (ToeplitzMatrix ... a_star) ≥ c_star`.
- `A3_Floor_Main.lean` — доказано `P_A_ge_c_star`.
- `UNIFORM_MIGRATION_PLAN.md` — план миграции, где смешаны `c_star` и `a_star`.
- `PERIOD1_FIX.md`, `PERIOD1_PATCH_CHECKLIST.md` — масштаб/периодизация `P_A` vs `ToeplitzMatrix` (потенциальная причина дрейфа).

### Процедура проверки (5 шагов)
1) Проверить, какой символ стоит в A3-аксиомах (`a_star` vs `P_A`).
2) Найти источник `c_star` (A3_FLOOR) и сравнить его домен/период.
3) Пройти цепочку A3_bridge → Q_nonneg и отметить, где меняется символ.
4) Проверить наличие мостов-заглушек (`c_star_le_c_arch`) и их роль.
5) Сверить периодизацию (period-1 vs 2π) по `PERIOD1_*` файлам.

Итог: если символы не совпадают, мост формально компилируется, но смысл уходит от Q3.

---

*Обновляй этот файл когда находишь новые insights!*
