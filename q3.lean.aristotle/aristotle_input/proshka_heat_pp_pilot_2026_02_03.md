# Proshka request: prime-heat PP bounds (pilot, buckets 0 & 99)

## Цель
Закрыть пилотный набор точечных неравенств для prime‑power термов:

```
prime_heat_weight_term n ≤ ((num : ℚ) / prime_heat_pp_term_ub_den : ℝ)
```

для фиксированного списка пар `(n, num)` из файла
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowPilotData.lean`.

Это пилот для замены аксиомы
`prime_heat_weight_term_le_pp_ub_of_prime_pow` в
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Checker.lean`.

## Контекст
Определение терма (из `BrangeHeatCert_2026_01_28_Data.lean`):

```
def prime_heat_weight_term (n : ℕ) : ℝ :=
  (w_Q n * (Real.exp (-4 * Real.pi ^ 2 * t_critical * (xi_n n) ^ 2) * |xi_n n|)) *
    (if |xi_n n| ≤ prime_cert_B_max then (1 : ℝ) else 0)
```

Фиксированные параметры:
- `t_critical = 3/20`
- `prime_cert_B_max = 4.9`
- `prime_heat_pp_term_ub_den` (из PrimePowData)

Пилотный список `(n, num)`:
- `prime_heat_pp_pilot_bucket_0_data`
- `prime_heat_pp_pilot_bucket_99_data`

Файл‑связка (пилотные обязанности):
`Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowPilot.lean`

## Ограничения
- В Mathlib **нет** тактики `interval` (проверено).
- `ComputableReal` не даёт `log`, поэтому не годится как прямой путь.
- Хотим Lean‑совместимую стратегию (монотонность, рациональные ограждения,
  `simp`/`ring`/`nlinarith`/`gcongr`), без `sorry`/`exact?`.

## Что нужно от Прошки
1) Реалистичная Lean‑стратегия для численных неравенств с `exp/log/sqrt` на
   фиксированных числах.
2) Минимальный proof‑skeleton (1‑2 примера на конкретном `n`, например `n=2`
   и `n=999983`), который можно масштабировать на список.
3) Как лучше “упаковать” эти доказательства: по‑леммно на каждый `n`, либо
   через общую лемму с монотонностью + таблица значений.

Формат ответа:
- 3–7 шагов стратегии
- 1‑2 коротких Lean‑фрагмента для конкретных чисел
- Указание, где и как автоматизировать список
