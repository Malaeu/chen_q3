# Линия Goldston и соавторов — парная корреляция, простые нули, нули на критической прямой

Четыре работы одной линии, затянуты 2026-08-11. Карточки собраны в один файл: работы
ссылаются друг на друга и порознь не читаются.

| bib-ключ | arXiv | авторы | дата версии |
|---|---|---|---|
| `SIEGFREDALANC…-2025` | `2501.14545v2` | Baluyot, Goldston, Suriajaya, Turnage-Butterbaugh | 21 ноя 2025 |
| `DANIELALANGOLDSTONANDJUNGHUNLEE…-2025` | `2503.15449v4` | Goldston, Lee, Schettler, Suriajaya | 30 мар 2026 |
| `DANIELAGOLDSTONANDADEIRMASURIAJAYA-2025` | `2511.20059v2` | Goldston, Suriajaya | 5 фев 2026 |
| `DANIELAGOLDSTONANDADEIRMASURIAJAYA-2026` | `2603.28104v1` | Goldston, Suriajaya | 30 мар 2026 |

---

## ⚠️ ЛОЖНЫЙ ДРУГ — читать до всего остального

**«Simple zeros» у них и `hsimple` у нас — РАЗНЫЕ ОБЪЕКТЫ.**

```
у них:  нуль ζ(s) кратности 1                     объект теории чисел, глобальный
у нас:  Module.finrank ℝ (eigenspace A ε) = 1     кратность собственного значения матрицы
```

Наш `hsimple` (вход `SIMPLE_EVEN`, `CCMFiniteWeilBottomSpectral.lean:61`) — про простоту
**нижнего собственного значения конечной CCM-матрицы**. Их «100% нулей просты» — про
кратность нулей дзеты. Совпадает только слово.

Аналогично «critical zeros» ≠ наш `ZerosRealOn`: у них нуль лежит на прямой `Re s = 1/2`,
у нас — нуль многочлена имеет `z.im = 0`. Связь между этими двумя есть, но она идёт через
мост `Ξ ⟺ RH` (`ClassicalXiInterface.lean`), а не через совпадение слов.

Эта запись существует, потому что поиск по слову `simple` тянет обе линии сразу.

---

## Карточка 1 — `2501.14545`: что даёт гипотеза «узкой вертикальной коробки»

**Что ДОСЛОВНО сказано** (абстракт):

> Here we assume a more general condition, namely that all the zeros `ρ = β + iγ` with
> `T < γ ≤ 2T` are in a **narrow vertical box centered on the critical line with width
> `b/log T`, where `b → 0` as `T → ∞`**. We first prove the generalization of Montgomery's
> result that at least `2/3` of zeros are simple, and we then prove the new result that the
> pair correlation method yields **at least `2/3` of the zeros on the critical line**. We
> also use the pair correlation method to prove that at least `1/3` of the zeros are both
> simple and on the critical line, a result already known unconditionally using different
> methods.

Точная формулировка коробки (цитируется в `2603.28104` как Теорема 1):

```
B_b = { s = σ + it : |σ − 1/2| < b / (2 log T),  T < t ≤ 2T,  b = b(T) → 0 при T → ∞ }
```

**Что это даёт НАМ.** Образец того, как гипотеза **слабее RH** конвертируется в
количественный результат. Это ровно жанр, в котором работает наш маршрут: мы тоже не
доказываем RH прямо, а строим цепь `A ∧ B ∧ C ⇒ RH`.

**Чего НЕ даёт.** Ни одной величины, входящей в наши слоты. Гипотеза «узкая коробка» — про
горизонтальное расположение нулей дзеты; у нас нет ни объекта `B_b`, ни высоты `T`.

---

## Карточка 2 — `2503.15449`: PCC без RH, и «горизонтальная кратность»

**Что ДОСЛОВНО сказано** (абстракт):

> Building on Montgomery's approach, Gallagher and Mueller proved in 1978 that PCC under RH
> implies that 100% of the zeros are simple. **Actually, the method of Gallagher and Mueller
> does not depend on RH**, and thus Montgomery's second simplicity conjecture follows
> unconditionally from his PCC conjecture… Using Gallagher and Mueller's method and a new
> idea concerning **"horizontal multiplicity"**, we use PCC to prove that asymptotically
> 100% of the zeros are not only simple but also on the critical line.

И прямо в §1: «In this paper we do not assume the Riemann Hypothesis (RH) is true or make
use of results that depend on RH.»

**Что это даёт НАМ.** Приём: снять RH из чужого доказательства, показав, что метод её не
использовал. Методологический образец, не поставщик.

**Чего НЕ даёт.** PCC (Pair Correlation Conjecture — гипотеза парной корреляции) сама
остаётся гипотезой. Результат условный, как и наш.

---

## Карточка 3 — `2511.20059` и `2603.28104`: где линия стоит сейчас

`2511.20059` (абстракт): «Here we show that **if RH could be removed** from Montgomery's
simple zero proof, then this would also give a proof that 2/3 of the zeros are simple and
on the critical line.» — то есть условное утверждение об условном утверждении.

`2603.28104` даёт «a simple proof based on a direct generalization of Montgomery's proof»
под той же гипотезой узкой коробки.

**Безусловное состояние области, дословно из `2511.20059` §1** — это самое ценное здесь:

> By a refined version of Levinson's method, K. Pratt, N. Robles, A. Zaharescu, and
> D. Zeindler [PRZZ20] in 2020 proved that **at least 41.7%** of the zeros of `ζ(s)` are on
> the critical line, and **at least 40.7%** of the zeros are on the critical line and simple.
> …Conditionally, under the RH assumption one can obtain that **at least 67.92%** of the
> zeros are simple using Montgomery's pair correlation method, and with a different method
> **at least 70.37%**.

И вычислительная граница:

> Platt and Trudgian [PT21] in 2021 showed that in the critical strip up to height
> `3,000,175,332,800`, there are exactly `12,363,153,437,138` zeros and **all of them are on
> the critical line and are simple**.

**Что это даёт НАМ.** Калиброванная шкала: безусловно — 41.7%, под RH — до 70.37%, численно
проверено до высоты `3·10¹²`. Это цифры, к которым уместно относить любое наше заявление о
прогрессе, чтобы не переоценивать частичный результат.

---

## Что НЕ прочитано

Прочитаны абстракты всех четырёх и введения `2511.20059`, `2603.28104`, плюс формулировка
коробки `B_b`. Доказательства, леммы и оценки не читаны ни в одной из четырёх.

**Статус:** контекст и калибровка, **не поставщики**. Ни одна из четырёх не входит ни в
один наш незакрытый шаг. Держать за ложным другом «simple zeros» — главная причина, по
которой карточка написана.
