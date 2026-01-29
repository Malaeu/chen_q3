# Proshka request: tau-shift arch floor (A3) for P_A_shift

## TL;DR
Нужна формальная лемма для **tau-сдвинутого** символа `P_A_shift`, чтобы закрыть
`Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`.

Сейчас готово:
- `Q3/Proofs/ShiftedWindows.lean`: `phi_shift`, `g_shift`, `P_A_shift`,
  `integral_P_A_shift_eq_arch_term` (arch_term = integral of P_A_shift).
- `A3_FLOOR_v22_stage4_floor.lean`: `P_A_ge_c_star` **только для** `P_A B_min t_sym` (tau=0).
- `Q3/Proofs/RKHS_cap_rayleigh.lean`: tau-кап (Variant 1) уже сделан.

Блокер: **arch floor для tau-сдвига** (нижняя оценка `arch_term (phi_shift ...)`).

## Что нужно от тебя
1) Подтвердить корректную **математическую формулировку** для tau-сдвига.
2) Дать **структуру доказательства** (или skeleton), чтобы перевести в Lean.
3) Сказать, нужно ли **править формулировку У3** (например, перейти на K-локальный floor).

## Текущая Lean-цель (идеал)
Вариант, максимально близкий к текущей архитектуре:

```lean
-- хотим что-то такого вида
lemma P_A_shift_ge_c_star
  (τ : ℝ) (hτ : |τ| + B_min ≤ K) :
  ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
    P_A_shift B_min t_sym τ θ ≥ c_star
```

Тогда через `integral_P_A_shift_eq_arch_term` получаем:
`arch_term (phi_shift B_min t_sym τ) ≥ c_star`.

## Если это НЕ верно
Тогда нужен **корректный K-зависимый floor**:

```lean
def c_star_K (K : ℝ) : ℝ := ...
lemma P_A_shift_ge_c_star_K
  (τ : ℝ) (hτ : |τ| + B_min ≤ K) :
  ∀ θ ∈ Set.Icc (-1/2 : ℝ) (1/2),
    P_A_shift B_min t_sym τ θ ≥ c_star_K K
```

и дальше проверяем, что `c_star_K/4 - rho_oneK K > 0`.

## Контекст файлов
- `A3_FLOOR_v22_stage4_floor.lean` — есть floor только при tau=0.
- `Q3/Proofs/ShiftedWindows.lean` — есть `P_A_shift` и arch integral.
- `Q3/Proofs/RKHS_cap_rayleigh.lean` — tau-кап (Variant 1, rho_oneK).

## Вопрос по тексту У3
Явно ли в У3 сказано, что floor **устойчив к сдвигу**?
Если да — нужна ссылка/лемма (например, "shift-robust core mass" / Lemma 8.13?).

Если нет — возможно, надо менять формулировку в У3:
1) переход на K-локальный floor,
2) grid→continuum (Lipschitz lift) вместо равномерного floor.

## Что от тебя нужно в ответе
- Четкая математическая формулировка (c_star или c_star_K).
- Минимальный набор лемм (какие оценки нужны).
- Скелет Lean-лемм (или хотя бы путь по существующим леммам/фактам).
