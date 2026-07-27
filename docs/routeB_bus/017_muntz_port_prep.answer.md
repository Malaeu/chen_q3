# ОТВЕТ 017 — MUNTZ_PORT_PREP

`MUNTZ_PORT_PREP_OK`

Статус маршрута: `CHALLENGER / NOT_RH`. `BUS_010_VOID` соблюдён.
Облачный код Мюнца не портирован.

## 1. Endpoint-мост

Файл: `Q3/Proofs/RouteB/WindowEndpointBridge.lean`.

```lean
theorem windowIntegral_Icc_eq_Ioo
    (f : ℝ → ℂ)
    (_hf : LocallyIntegrable f)
    {A B : ℝ}
    (_hA : 0 < A)
    (_hAB : A < B) :
    (∫ u : ℝ in Icc A B, f u) = ∫ u : ℝ in Ioo A B, f u
```

Доказательство использует более сильную готовую теорему Mathlib
`MeasureTheory.integral_Icc_eq_integral_Ioo`: Lebesgue volume атомов не имеет,
поэтому значения в двух концах не влияют на set integral.

Интерфейс специально сохраняет `LocallyIntegrable f` и `0 < A < B`, чтобы
будущий облачный `Gwin` сел на локальное `windowedMellin` без изменения
контракта.

## 2. Равенство Mellin-конвенций

```lean
theorem integral_mul_cpow_eq_mellin
    (k : ℝ → ℂ)
    (s : ℂ) :
    (∫ u : ℝ in Ioi 0, k u * (u : ℂ) ^ (s - 1)) = mellin k s
```

После раскрытия `mellin` Mathlib-интегранд равен
`(u : ℂ) ^ (s - 1) • k u`. Для комплексных значений `smul_eq_mul`, а смена
порядка множителей — `mul_comm`. Дополнительных предположений о сходимости
для этого равенства определений не требуется.

## 3. Нотариат Lean

- Строк в `WindowEndpointBridge.lean`: `39`.
- Новых теорем: `2`.
- `sorry|exact?|admit|native_decide|implemented_by`: `0`.
- `lake build Q3.Proofs.RouteB.WindowEndpointBridge`: exit `0`.
- Полный `lake build`: exit `0` (`7817 jobs`).
- `#print axioms windowIntegral_Icc_eq_Ioo`:
  `[propext, Classical.choice, Quot.sound]`.
- `#print axioms integral_mul_cpow_eq_mellin`:
  `[propext, Classical.choice, Quot.sound]`.

## 4. Зеркало Прошки

Ручной `KEY_LEAN` удалён. Скрипт теперь перечисляет
`Q3/Proofs/RouteB/*.lean` и fail-closed останавливается, если каталог пуст.

- Lean-файлов Route B в зеркале: `53/53`.
- Всего mirrored sources: `120`.
- Файлов с метаданными: `122`.
- `ProlateLayer.lean`: присутствует в `MANIFEST.md`.
- `WindowEndpointBridge.lean`: присутствует в `MANIFEST.md`.
- Immutable code/whitelist mirror commit:
  `6656e6a01429adea7cd6180053d8026c292762a7`.
- Diff этого коммита вне `docs/routeB_bus/`: `0`.
- Push `rh_clean`: fast-forward, success.

Последующий механический синк самого этого отчёта может продвинуть head
зеркала; SHA выше — коммит, который исполнил пункт 3 и впервые опубликовал
полный Lean-whitelist.

## Граница результата

Закрыты только endpoint- и Mellin-конвенционные адаптеры плюс видимость всех
Route-B Lean-файлов. `RIEMANN_SUM_LIPSCHITZ_GAP` и
`ESTAR_CONTINUATION_LEMMA_MISSING` не закрыты; облачный Müntz-файл в локальное
дерево не переносился.

Итог: `MUNTZ_PORT_PREP_OK`.
