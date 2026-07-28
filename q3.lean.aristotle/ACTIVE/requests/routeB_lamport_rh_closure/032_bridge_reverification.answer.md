# ОТВЕТ 032 — BRIDGE LOCAL REVERIFICATION

`BRIDGE_LOCAL_REVERIFIED`

Статус: `CHALLENGER / NOT_RH`.

## Source-lock

```text
7161d7376c3d9c7142c9a92a89a9ec8434fe73260019837de2d2f7b95749d039  ARISTOTLE_TASK_RiemannBoundaryCellBridge.md
d47a0e1d1c3aa81b7f140db6103c64e553085df5542678c87c96c4cbbe19d3c7  RequestProject/RiemannBoundaryCellBridge.lean
b1481968ce2912f2b85288fc18aa05fb22750e4083f9e03f49f59a8814ba268a  lakefile.toml
db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028  lean-toolchain
116c6ef00aa899fb38c08c5e4c92c0e434d0e7f9d574fcb5d4d42cc90ffb07cb  lake-manifest.json
```

## Свежая локальная сборка

Scratch: `/tmp/routeb032_bridge.ChfIB8`; mainline `.lake` не
переиспользовался. После нотариата scratch удалён.

```text
ℹ [8027/8029] Replayed RequestProject.BridgeAxiomAudit
Build completed successfully (8029 jobs).
LAKE_BUILD_EXIT=0
```

Гвард по доставленным `Main.lean` и
`RiemannBoundaryCellBridge.lean`:

```text
sorry/admit/axiom/native_decide matches = 0
```

## `#print axioms` — вывод дословно

```text
info: RequestProject/BridgeAxiomAudit.lean:3:0: 'riemannBoundaryCellBridge_finiteReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/BridgeAxiomAudit.lean:4:0: 'riemannBoundaryCellBridge_main' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/BridgeAxiomAudit.lean:5:0: 'riemannBoundaryCellBridge_zeroMass' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RequestProject/BridgeAxiomAudit.lean:6:0: 'riemannBoundaryCellBridge_Estar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Дословная семантическая сверка T0–T3

| Контракт | Lean-формулировка | Итог |
|---|---|---|
| T0: `tsum` по `ℕ+` равен сумме по `Finset.Icc 1 (Nat.ceil (b/u))`; точное попадание в `b` сохраняется | `riemannBoundaryCellBridge_finiteReduction`, строки 14–18 | MATCH |
| T1: явная константа `u * (K*b + (‖h 0‖+K*b) + ‖h b‖)` | `riemannBoundaryCellBridge_main`, строки 195–202 | MATCH |
| T1: `LipschitzOnWith K h (Set.Ico 0 b)`, не на замкнутом носителе | строки 198, 325, 339; вспомогательные cell-леммы также используют `Ico` | MATCH |
| T1: никакого ослабления до `∃ C` | публичный вывод содержит ту же явную константу | MATCH |
| T2: zero-mass bound без множителя `u` | `riemannBoundaryCellBridge_zeroMass`, строки 321–333 | MATCH |
| T3: `u ∈ Ioo 0 1` и множитель `Real.sqrt u` | `riemannBoundaryCellBridge_Estar`, строки 335–349 | MATCH |

`Set.Icc 0 b` в файле относится к гипотезе компактного носителя и
интегрируемости; оно не подменяет требуемую одностороннюю область
липшицевости `Set.Ico 0 b`.

## Mathlib API, реально использованный доказательством

1. Разбиение интеграла на `Ioc`-ячейки:
   `intervalIntegral.sum_integral_adjacent_intervals` и
   `intervalIntegral.integral_add_adjacent_intervals`.
2. Сведение `tsum` к конечной сумме: `tsum_eq_sum`.
3. Липшицева оценка ячейки:
   `LipschitzOnWith.norm_sub_le` вместе с
   `intervalIntegral.norm_integral_le_of_norm_le_const` и
   `intervalIntegral.norm_integral_le_of_norm_le_const_ae`.

## Интеграция

- Compiler ledger: `RiemannBoundaryCellBridge`,
  `status=PROVED`, `scope=ABSTRACT`, `verifier=LEAN`,
  безусловный машинно проверенный пакет T0–T3.
- Зеркало правила 014 включает контракт, goal/answer и каталог
  `aristotle_bridge/`.
- `STATE` не изменён.
- Bus 010 не создан.
