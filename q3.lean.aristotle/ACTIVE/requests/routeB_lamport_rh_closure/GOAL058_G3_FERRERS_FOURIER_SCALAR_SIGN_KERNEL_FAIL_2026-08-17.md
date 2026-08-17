# Goal 058 G3 — Ferrers Fourier scalar sign: kernel check FAILED

Date: 2026-08-17
Branch: `rh_clean`
Pinned HEAD at entry: `c4d1d98fddfb`
Route state: `CHALLENGER_NOT_RH`
RH_CLAIM: `false`

## Первое: канал записи сменился

Этот узел **Прошка записал в репозиторий сам**, через GitHub API. Не пересказал
в чат — положил коммитом. Первый такой случай.

Отличие его записей от наших, проверено на этом коммите:

```
Прошка:  146065732+Malaeu@users.noreply.github.com   ← веб/API GitHub
мы:      kdl2026@dfr.de                              ← локальный git config
```

Следствие для работы: вердикт теперь можно **проверять ядром**, а не разбирать
описание. Что и вскрыло проблему ниже — по пересказу она была бы невидима.

## Что заявлено

```yaml
PRIMARY: FERRERS_FOURIER_SCALAR_SIGN_REDUCED_TO_CENTER_SIGN
commit: c4d1d98fddfb634dad050afc3959955b6de886e3
file:   q3.lean.aristotle/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierScalarSign.lean
VERIFIER:
  source_audit: PASS
  mathematical_identity: PASS
  lean_kernel_check: PENDING     # ← честно помечено как непроверенное
```

Публичные теоремы:
- `Mode4FerrersRegularEvenProlateSolution.exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul_and_mul_center_pos`
- `Mode4FerrersRegularEvenProlateSolution.physicalFiniteFourier_scalar_pos_iff_center_pos`

Содержание: из `χ · f(0) = √m · 2a₀` и `a₀ > 0`, `m ≥ 2` следует `χ · f(0) > 0`,
значит `χ > 0 ⟺ f(0) > 0`. Положительная фаза сведена к знаку в центре.

## Что показала проверка ядром

`lean_kernel_check` закрыт со стороны Mac. Результат — **FAIL**.

```
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign

error: D0Mode4FerrersPhysicalFourierScalarSign.lean:47:2: `simp` made no progress
error: Lean exited with code 1
error: build failed
```

Обе публичные теоремы опираются на заглушку:

```
'…exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul_and_mul_center_pos'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

'…physicalFiniteFourier_scalar_pos_iff_center_pos'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

Для сравнения, здоровый узел из той же цепи (`…NonzeroScalar.lean`) опирается
только на `[propext, Classical.choice, Quot.sound]` — без `sorryAx`.

### Ловушка, которую стоит записать отдельно

Слова `sorry` в тексте файла **нет ни одного**. Поиск по тексту даёт чисто.

`sorryAx` появился от упавшей тактики: Lean не бросает файл на ошибке, а
затыкает место заглушкой и идёт дальше. Снаружи выглядит доказанным.

```
grep "sorry"            → чисто        ← обманка
axioms: [… sorryAx …]   → дырка есть   ← правда
```

Проверять надо `#print axioms` или строки `depends on axioms` в логе сборки,
а не текст файла.

### Точка отказа

Строка 47:

```lean
simpa only [mode4PhysicalFerrersSeries, s, smul_eq_mul] using hscale
```

`simp` не находит, что упрощать. Вероятные причины: `mode4PhysicalFerrersSeries`
уже развёрнут к этому моменту, либо локальное `s` не редуцируется как ожидалось.
Это техника, не математика — тождество выглядит корректным.

## Статус узла, честно

| Поле | Заявлено | По факту |
|---|---|---|
| `lean_kernel_check` | PENDING | **FAIL** |
| теоремы | записаны | записаны, но **на sorryAx** |
| `scalar_sign_relation` | SOURCE_WRITTEN | верно: написано, не доказано |
| аксиом добавлено | 0 | 0 — подтверждаю, `axiom` в файле нет |

`SOURCE_WRITTEN` не оспаривается: файл существует, 138 строк, один файл в
коммите. Ложным было бы объявить его доказанным — Прошка этого и не делал.

## Что требуется

1. Починить строку 47 так, чтобы `lake build` прошёл без `sorryAx`.
2. Повторно снять `#print axioms` для обеих публичных теорем.
3. Только после зелёной сборки считать `scalar_sign_relation` закрытым.

Следующий узел по директиве (`center_pos_of_no_interior_zero`) писать **после**
починки: он опирается на эти две теоремы, и на заглушке цепь не выстроится.

## Команда проверки

```bash
cd q3.lean.aristotle
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign
```

Признак успеха: в выводе нет `sorryAx` ни у одной из двух публичных теорем.
