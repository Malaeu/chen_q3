# Aristotle Müntz v3 PoleSubtracted — харвест

Проект `987ff124-3032-42e5-aa9f-24ceef69f62a`, задача
`472e126c-759f-4c69-8816-fa013ff740b2`, статус `COMPLETE_WITH_ERRORS`, 100%.
Скачано в `q3.lean.aristotle/aristotle_output/987ff124_MUNTZ_V3_POLESUBTRACTED_2026-07-30/`.

## Вердикт по Lean-исходникам (не по RESULT.md)

`RequestProject/Main.lean`, 239 строк:

- `rg "sorry|admit|native_decide|exact?"` — **ноль вхождений**
- сборка успешна
- аксиомы проверенных деклараций: ровно `propext`, `Classical.choice`, `Quot.sound`
- новых аксиом нет

То есть `COMPLETE_WITH_ERRORS` здесь означает не грязный код, а **недостигнутую
цель при чистом коде**.

## Что доказано — условно

Pole-subtracted слой собран целиком, но **условно на Mellin-аналитичности**:

- dslope-тождества и аналитичность
- расширение residue-фактора через `riemannZeta_residue_one` и
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
- аналитичность произведения, off-pole равенство, значение в полюсе
- склейка по теореме единственности на связной полуплоскости через
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`
- punctured/pole-value следствия

## Что НЕ доказано

`T4a`, и следовательно безусловные `T5` и пакет `PL1–PL3`.

## Названный gap — точная формулировка

Код: `MELLIN_DSLOPE_ANALYTICITY_GAP` (тот же, на который упёрся R5).

Недостающее утверждение выписано дословно:

```lean
AnalyticOnNhd ℂ (fun s ↦ ∫ u in Set.Ioi (0 : ℝ), h u * (u : ℂ) ^ (s - 1)) {s | 0 < s.re}
```

из гипотез: `Measurable h`, носитель в `Set.Icc 0 b`,
`LipschitzOnWith K h (Set.Ico 0 b)`.

## Замечание кондуктора

Это второй заход в ту же стену (R5 дал тот же код), но с прибылью: раньше был
код без адреса, теперь есть точное утверждение, которое можно заказать
отдельным контрактом или искать в Mathlib. Стена не сдвинулась — она обмерена.

Харвест ≠ потребление. Потребление — отдельная транзакция, гол 039+, как
постановил диспетчер.
