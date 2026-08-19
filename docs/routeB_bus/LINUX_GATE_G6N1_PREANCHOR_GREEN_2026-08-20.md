# STATUS: GREEN — G6N1 PRE-ANCHOR TRANSACTION KERNEL-VALIDATED AFTER FOUR NIGHT ROUNDS

```yaml
PRIMARY: G6_N1_PREANCHOR_LIMIT_ZERO_MODE_AND_SELECTED_SHELL_LEAN
GATE_RUN_BY: LINUX_BODY_NIGHT_LOOP
NIGHT_GRANT: NIGHT_GRANT_2026-08-20
TRAJECTORY: 36 -> 5 -> 2 -> 0 errors over commits ccb664b6, 02d21ef9, cfee730a, 7e573a2d
FINAL_LEAN_SHA256: 88cfc9dea2fa24a1f3a93531d402d3d6a95e7c348cffb9d944b1840bc1f94636
AXIOMS_ALL_NINE: [propext, Classical.choice, Quot.sound]
WARNINGS: 0
Q3_CHECK: ok
CLOSES:
  - CCM_LEMMA_7_3_SELECTED_MUNTZ_LIMIT          # узел G6-N1
  - SELECTED_FINITE_PROLATE_CENTRAL_NONVANISHING # ремонт N0
KEY_THEOREMS:
  - trialNonzero_of_preAnchorGwin_zero_ne
  - eventually_preAnchorGwin_zero_ne
  - selectedProlateCofinalSourceDataOfPreAnchorPort   # свидетель существует!
  - SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi
  - SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor
G6_REMAINS: wall N2 (Mellin compact decay) + two assemblies
ROUTE: CHALLENGER_NOT_RH · BUS_010_VOID · PX_RH_CLAIM_NOT_MADE
```

Четыре ночных оборота петли: источник -> красный 36 -> починка -> красный 5 ->
перестройка на этажи -> красный 2 (одна тяжёлая лемма) -> разбивка последнего
этажа -> ноль. Все правки — судьи; Linux-тело только гейтовало и возвращало
точные диагнозы. Свидетель ProlateCanonicalSourceData существует, кофинальность
и центральная невырожденность выведены, предел Мюнца к centeredXi доказан на
production-расписании.
