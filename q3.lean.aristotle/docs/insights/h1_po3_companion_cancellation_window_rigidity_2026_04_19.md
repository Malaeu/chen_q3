# `PO3-rig.1` companion-cancellation rigidity on compressed windows (2026-04-19)

## Статус

Частично формализовано.

Это не доказательство всей ветки `PO3`, а точная заморозка следующего
содержательного узла после закрытия локального `PO3-shell`.

### Update (Lean, 2026-04-19)

Абстрактное ядро `PO3-rig.1a` уже посажено в Lean как
`Q3.HBridge.po3_rankOne_companion_rigidity` в файле
`Q3/Proofs/HBridge_PO3_Shell.lean`.

Формальная форма сейчас такая:

```tex
\phi\otimes x + \psi\otimes u = 0,\qquad \phi\neq 0,\quad u\neq 0
\Longrightarrow
x\in \mathbb C u,\ \psi\in\mathbb C\phi.
```

Это именно тот конечномерный линейно-алгебраический пакет, который нужен для
оконной жёсткости: одна фиксированная ненулевая функциональная нога и одна
фиксированная ненулевая векторная нога forcing обе свободные ноги в
соответствующие одномерные линии.

Значит следующий содержательный шаг уже не в `1a`, а в честной привязке
реального surviving packet к этой abstract rank-one форме и затем в склейке
оконных констант.

### Update (Lean, 2026-04-19, second pass)

Abstract shell для `PO3-rig.1b` теперь тоже посажен в Lean.

Добавлены две леммы:

- `Q3.HBridge.po3_coordinate_profile_of_mem_span_singleton`;
- `Q3.HBridge.po3_coordinate_profile_of_rankOne_companion_rigidity`.

Их смысл ровно такой:

```tex
x \in \mathbb C u
\quad\Longrightarrow\quad
\text{любой координатный профиль }x\text{ есть }c\text{-кратный профиль }u,
```

а значит после `PO3-rig.1a` и заданного coordinate certificate для
compressed endpoint vector уже автоматически получается один оконный закон

```tex
w_r = c_{a,N,M}\,\sigma_r.
```

Для `PO3` это означает: abstract часть перехода

```tex
x_M \in \mathbb C u_{+,M,N}
\Longrightarrow
w_{r,0}(a)=c_{a,N,M}(-1)^r
```

теперь формально сведена к одной generic coordinate lemma.

Значит живой остаток `PO3-rig.1b` уже не линейно-алгебраический:
осталось только честно дать реальный Q3-side coefficient certificate для
compressed zero-mode column `v_{a,N}`.

### Update (Lean, 2026-04-19, third pass)

Shell для `PO3-rig.1b` теперь закрыт полностью.

Добавлены ещё две леммы:

- `Q3.HBridge.po3_scalar_eq_of_shared_coordinate_profile`;
- `Q3.HBridge.po3_shared_coordinate_profile_of_two_mem_span_singleton`.

Их смысл такой:

```tex
\text{если одна и та же последовательность }w_r
\text{ равна }c_+ \sigma_r\text{ и }c_- \sigma_r,
\text{ а }\sigma\text{ где-то ненулевая, то }c_+=c_-.
```

Значит из двух span-laws на плюс- и минус-окне и из общей кодирующей
последовательности автоматически получается **один** общий оконный скаляр.

Это именно тот abstract reflection-even / shared-sequence bridge, которого
не хватало, чтобы довести `PO3-rig.1b` до конца на shell-уровне.

Следовательно, следующий настоящий live brick уже не про shell:
нужно либо ввести в Lean реальные объекты `v_{a,N}` и `w_{r,0}(a)`,
либо посадить отдельный Q3-side certificate layer, который честно подаст их
в этот уже закрытый shell.

## Где этот узел в лестнице

См. также:

- [`h1_po3_route_ladder_2026_04_19.md`](/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/insights/h1_po3_route_ladder_2026_04_19.md)

После `PO3-shell.6` следующий честный шаг уже не про API и не про упаковку,
а про одну точную оконную жёсткость:

```tex
\text{exact first-order companion cancellation on }(N,M]
\Longrightarrow
w_{r,0}(a)=c_{a,N,M}(-1)^r
\quad (N<r\le M).
```

Именно это мы называем `PO3-rig.1`.

## Почему это правильный следующий узел

У нас уже заморожены три факта:

1. живой объект — это один zero-mode column
   `v_{a,N}=T_{a,\infty,N}^*G_g[a]\mathbf 1`;
2. его координаты на хвосте равны `\sqrt{2a}\,w_{r,0}(a)`;
3. surviving first-order route обязан идти через cancellation с adjoint
   companion term, а не через одинокий endpoint brick.

Значит следующий узел не должен быть “общая новая теория boundary algebra”.
Он должен быть ровно про то, что такое cancellation уже forced на одном
конечном окне.

## Рабочая theorem-shape

Ниже зафиксирован пакет из трёх локальных целей.

### `PO3-rig.1a`  `[Абстрактная оконная жёсткость]`

Фиксируем окно `N<r\le M` и обозначения

```tex
u_{+,M,N}
:=
\frac{1}{\sqrt{2a}}\sum_{r=N+1}^{M}(-1)^r e_r^+,
\qquad
u_{-,M,N}
:=
\frac{1}{\sqrt{2a}}\sum_{r=N+1}^{M}(-1)^r e_r^-.
```

Это Riesz-векторы compressed endpoint-functionals
`\ell_{+,N}P_+` и `\ell_{-,N}P_-` на данном окне.

Пусть surviving first-order packet на окне имеет вид

```tex
K_v^{(M)} + (K_v^{(M)})^*,
\qquad
K_v^{(M)}:=P_{M,N}\,v\otimes(\ell_{+,N}P_+ + \ell_{-,N}P_-)\,P_{M,N}.
```

Тогда его mixed block равен

```tex
P_+\bigl(K_v^{(M)} + (K_v^{(M)})^*\bigr)P_-
=
x_M\otimes u_{-,M,N} + u_{+,M,N}\otimes y_M,
```

где

```tex
x_M:=P_+P_{M,N}v,
\qquad
y_M:=P_-P_{M,N}v.
```

Точная цель:

```tex
P_+\bigl(K_v^{(M)} + (K_v^{(M)})^*\bigr)P_- = 0
\Longrightarrow
x_M \in \mathbb C\,u_{+,M,N}
\text{ and }
y_M \in \mathbb C\,u_{-,M,N}.
```

### Доказательство-скелет для `1a`

Нужно не угадывать коэффициенты, а бить линейной алгеброй через kernel
functionals.

Если `y_M \notin \mathbb C\,u_{-,M,N}`, то существует вектор `z_-` в минусовом
окне такой, что

```tex
\langle z_-,u_{-,M,N}\rangle = 0,
\qquad
\langle z_-,y_M\rangle \neq 0.
```

Тогда

```tex
\bigl(x_M\otimes u_{-,M,N} + u_{+,M,N}\otimes y_M\bigr)(z_-)
=
\langle z_-,u_{-,M,N}\rangle x_M + \langle z_-,y_M\rangle u_{+,M,N}
=
\langle z_-,y_M\rangle u_{+,M,N}.
```

Если mixed block нулевой и `u_{+,M,N}\neq 0`, это невозможно.
Значит `y_M \in \mathbb C\,u_{-,M,N}`.

Симметрично доказывается

```tex
x_M \in \mathbb C\,u_{+,M,N}.
```

Итак, `PO3-rig.1a` — это чистая линейная алгебра конечного окна.

### `PO3-rig.1b`  `[Специализация к zero-mode column]`

Теперь подставляем `v=v_{a,N}`.

По уже замороженной reflection-evenness координаты `v_{a,N}` на плюс- и
минус-хвостах кодируются одной и той же последовательностью `w_{r,0}(a)`
с alternating sign convention.

Поэтому из

```tex
x_M \in \mathbb C\,u_{+,M,N},
\qquad
y_M \in \mathbb C\,u_{-,M,N}
```

следует существование одного скаляра `c_{a,N,M}` такого, что

```tex
w_{r,0}(a)=c_{a,N,M}(-1)^r
\qquad (N<r\le M).
```

Это и есть точная формулировка `PO3-rig.1`.

### `PO3-rig.1c`  `[Интерфейс к `PO3-tail.1`]`

Следующий узел уже не про линейную алгебру, а про согласование окон.

Если одно и то же first-order cancellation требуется на двух окнах
`(N,M_1]` и `(N,M_2]` с `M_1<M_2`, то на пересечении окон оба закона дают
одинаковые значения `w_{r,0}(a)`.

Значит автоматически

```tex
c_{a,N,M_1}=c_{a,N,M_2}.
```

Это и есть точка входа в `PO3-tail.1`:
оконные константы glue on overlaps и дают один tail constant `c_{a,N}`.

## Что здесь уже механика, а что ещё стена

### Уже механика

- extraction of `x_M`, `y_M`, `u_{+,M,N}`, `u_{-,M,N}`;
- abstract finite-window linear algebra of `1a`
  through `Q3.HBridge.po3_rankOne_companion_rigidity`;
- overlap gluing statement `1c`.

### Ещё не механика

- честный вход из реального `PO3` packet в exact companion-cancellation
  hypothesis на каждом окне;
- затем уже глобальная impossibility route
  `c_{a,N}=0` и переход к Cauchy/square-tail nodes.

То есть `PO3-rig.1` не является главной стеной. Это последний узкий
локальный узел перед `PO3-tail.*` и `PO3-cauchy.*`.

## Failure mode

Если при попытке честной формализации выяснится, что mixed block surviving
packet не имеет exact form

```tex
x_M\otimes u_{-,M,N} + u_{+,M,N}\otimes y_M,
```

или что reflection-evenness недостаточна для склейки двух сторон в один
скаляр `c_{a,N,M}`, то это уже не проблема оформления.
Это будет означать, что текущая first-order route была сжата слишком
агрессивно и требует возврата к более точной packet form на уровне `PO3a.4`.

## Ближайший практический выход

Самый честный следующий formal move такой:

1. привязать surviving mixed packet на окне к форме
   `\phi\otimes x + \psi\otimes u`;
2. отдельно записать specialization `PO3-rig.1b` к zero-mode column;
3. сразу после этого открыть `PO3-tail.1` как gluing lemma для
   `c_{a,N,M}`.

То есть следующий кодовый шаг не должен пытаться доказать весь tail-zero
route сразу. Надо сначала посадить один clean rigidity packet.
