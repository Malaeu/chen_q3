# PROSHKA REQUEST — A3 Floor at t_critical (single‑scale)

## Non‑negotiable policy
- Не ищи «статус RH». RH не доказана публично, мы доказываем её сами.
- Никаких внешних источников. Работай **только** с нашим контекст‑паком и файлами проекта.
- Не изобретай новые теоремы: либо копируй/адаптируй уже существующую логику A3_Floor_Main, либо честно говори, где упираешься.

## Цель (Lean)
Закрыть `FloorGoal` на single‑scale:

```lean
-- файл: Q3/Proofs/A3_Floor_Critical_Proof.lean (можно новый)
import Q3.Proofs.A3_Floor_Critical_Goal
import Q3.Proofs.A3_Floor_Main
import Q3.Proofs.Params_Critical

open Q3

 theorem A3FloorCritical.floor_goal_tcritical : Q3.Proofs.A3FloorCritical.FloorGoal := by
   -- proof
```

где

```lean
def Q3.Proofs.A3FloorCritical.FloorGoal : Prop :=
  ∀ θ ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2),
    Q3.c_star ≤ P_A B_min Q3.t_critical θ
```

## Контекст
- На `t_sym` это **уже доказано** в `Q3/Proofs/A3_Floor_Main.lean` (см. `P_A_ge_c_star`).
- На `t_critical = 3/20` нужно доказать аналогично.
- Мы уже завели мосты:
  - `arch_term_ge_at_t_critical` (теперь требует floor‑гипотезу)
  - `rayleigh_basis0_shift_ge_cstar_quarter_Bmin` (готов, если есть FloorGoal)

## Требование к результату
Нужен **чистый Lean‑код без `sorry`**, который реально компилируется. Лучше маленькая серия лемм, чем один огромный блок.

## Предпочтительный подход
**Скопировать/адаптировать доказательство `P_A_ge_c_star` из `A3_Floor_Main` на `t_critical`.**

Какие куски, вероятно, нужно продублировать с заменой `t_sym → t_critical`:
- `w_lower_on_half` (или эквивалент нижней оценки w на [-1/2,1/2])
- `g0_lower`, `g1_lower`, `g2_lower`, `g_neg1_lower`, `g_neg2_lower`, `g_neg3_lower`
- финальная сборка в `P_A_ge_c_star`

> Важно: это **не** монотонность по t. Нужна переработка оценок с новыми числовыми константами.

## Что именно нужно от тебя (Proshka)
1) Список конкретных лемм, которые нужно портировать (с точными именами из `A3_Floor_Main`).
2) Минимальный Lean‑скелет (код) для `floor_goal_tcritical` + подпроцедур.
3) Если какая-то оценка ломается, явно укажи где и почему (и что надо подправить в числах).

## Где смотреть
См. контекст‑пак:
`ACTIVE/output/proshka_context_floor_tcritical.md`

Ключевые файлы:
- `Q3/Proofs/A3_Floor_Main.lean`
- `Q3/Proofs/A3_Floor_Critical_Goal.lean`
- `Q3/Proofs/Params_Critical.lean`
- `Q3/Proofs/Q_nonneg_t_critical.lean`

## Формат ответа
- Сначала **план и карта лемм** (bullet list)
- Затем **Lean‑скелет**
- Затем **список мест, где нужны численные константы**

