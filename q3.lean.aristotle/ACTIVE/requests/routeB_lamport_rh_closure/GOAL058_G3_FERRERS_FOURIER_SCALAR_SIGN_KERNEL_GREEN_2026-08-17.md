# Goal 058 G3 — Ferrers Fourier scalar sign: ядро зелёное

Date: 2026-08-17
Branch: `rh_clean`
Base at entry: `ade5150b` (HEAD Прошки после его repair-коммита)

## Итог

```
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign
Build completed successfully (7783 jobs).

exists_physicalFiniteFourierAction_eq_real_nonzero_scalar_mul_and_mul_center_pos
  depends on axioms: [propext, Classical.choice, Quot.sound]
physicalFiniteFourier_scalar_pos_iff_center_pos
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sorryAx` нет ни у одной. Оба условия repair-gate выполнены.

## Ошибка в моём предыдущем отчёте — исправляется здесь

Отчёт `..._KERNEL_FAIL_2026-08-17.md` назвал точку отказа так:

```
Строка 47:
simpa only [mode4PhysicalFerrersSeries, s, smul_eq_mul] using hscale
```

Номер `47` был взят из лога сборки и был **верным**. Текст под ним — со
**строки 45**, соседней. Две строки не совпадали, и это моя ошибка записи.

Прошка починил то, что было написано текстом (строка 45), а не то, на что
указывал номер. Его правка сама по себе корректна и сборку не ломает, но
падавшее место не трогала: после неё файл вырос на 4 строки и та же ошибка
переехала на 51.

Правило на будущее: **в отчёт о падении класть строку, скопированную из файла
по тому самому номеру**, а не по памяти о соседнем содержимом.

## Настоящая точка отказа

Строка 47 старой нумерации (51 после правки Прошки):

```lean
simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
```

Цель на этот момент — снята `trace_state`:

```
⊢ ∫ (y : ℝ) in Icc (-√↑mProject) √↑mProject,
      cexp (I * ↑(2 * Real.pi * 0 * y))
        * mode4PhysicalFerrersSeriesComplex mProject S.coefficients y
    = ↑(√↑mProject * (2 * S.coefficients 0))
```

Нуль сидит **внутри** вещественного произведения: `2 * Real.pi * 0 * y`,
то есть `(2 * π * 0) * y`. Чтобы до него добраться, первым нужен `mul_zero`
(`2 * π * 0 → 0`), и только потом работают `zero_mul`, `Complex.ofReal_zero`,
`Complex.exp_zero`, `one_mul`.

`mul_zero` в списке не было. Ни одна из четырёх перечисленных лемм не находила
своего образца, `simp only` не делал ни одного шага — отсюда буквальное
`simp made no progress`.

## Правка

```lean
-  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
+  simp only [mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero, one_mul]
```

После этого вскрылся второй, зависимый дефект: `rw [...integral_ofReal,
hphysical]` закрывает цель полностью, и завершающий `rfl` падал с
`No goals to be solved`. Он был мёртв всё это время — просто до него не
доходило исполнение.

```lean
   rw [intervalIntegral.integral_ofReal, hphysical]
-  rfl
```

Обе правки — техника. Формулировки теорем, определения и математическое
содержание не менялись; правка Прошки в `hphysical` сохранена как есть.

## Что это открывает

`scalar_sign_relation` закрыт по-настоящему: знак положительной фазы сведён
к знаку в центре, и цепь стоит на ядре, а не на заглушке.

Следующий узел по директиве — `center_pos_of_no_interior_zero` — разблокирован:
запрет «не начинать до чистого axiom-profile» снят выполнением условия.

## Команда воспроизведения

```bash
cd q3.lean.aristotle
rm -f .lake/build/lib/lean/Q3/Proofs/RouteB/D0Mode4FerrersPhysicalFourierScalarSign.olean
lake build Q3.Proofs.RouteB.D0Mode4FerrersPhysicalFourierScalarSign
```

Удаление `.olean` обязательно: без него Lake отдаёт `Replayed` из кэша и
профиль аксиом печатается по старой сборке.
