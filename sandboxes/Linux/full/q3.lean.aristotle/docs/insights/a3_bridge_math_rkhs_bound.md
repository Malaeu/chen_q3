# A3 Bridge Mathematics

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
