According to a document from July 11, 2026, `H2a` всё ещё означает **существование простого изолированного чётного ground eigenvector**, а theorem о вещественности нулей его преобразования остаётся условным на `H2a`. Поэтому твоя лемма может быть полностью независимой от `H2a` как **теорема инъективности источника**, но для закрытия самого `H2a` нужен ещё отдельный мост: каждый допустимый ground vector должен порождать один и тот же канонический (A). 

# STATUS: PROVED после уточнения области

```text
CLAIM_V2:
  ACCEPTED AS SOURCE-INJECTIVITY THEOREM

H2a:
  NOT AUTOMATICALLY CLOSED

REAL-ZERO HYPOTHESIS:
  REDUNDANT

RH:
  NOT_RH
```

Физический `SOFT_L2_EVEN_REAL_SOURCE_DETERMINATION_CLAIM_V2.md` в доступном мне корпусе не найден, поэтому ниже я проверяю ровно изложенный тобой скелет.

Главный результат:

[
\boxed{
\text{в классе вещественных чётных компактно поддержанных источников}
}
]

[
\boxed{
\text{полная автокорреляция определяет источник с точностью до общего знака.}
}
]

Никакого третьего класса двойников внутри этого класса нет. Якорь фиксирует знак.

Причём лучший proof-route проще твоего square-root-маршрута и не требует анализа монодромии.

---

# 1. Сильнейшая и самая дешёвая формулировка

Пусть (p,q\in L^2(\mathbb R)) удовлетворяют:

[
p,q\ \text{вещественны},
\qquad
p(-u)=p(u),\quad q(-u)=q(u),
]

и имеют компактный носитель.

Определим:

[
\widetilde q(u):=\overline{q(-u)}=q(u),
]

[
A_q:=q*\widetilde q,
]

и аналогично (A_p).

## Теорема — `EvenRealFullAutocorrelationRigidity`

Если

[
A_p=A_q
]

как функции или tempered distributions на всей (\mathbb R), то

[
\boxed{p=q\quad\text{или}\quad p=-q.}
]

Если дополнительно задан один линейный якорь (\ell), для которого

[
\ell(p)=\ell(q)=a\ne0,
]

то

[
\boxed{p=q.}
]

## Доказательство

Пусть:

[
F=\mathcal Fq,
\qquad
G=\mathcal Fp.
]

Компактный носитель даёт целые продолжения (F,G).

При точной Fourier-конвенции существует фиксированная ненулевая константа (c_{\mathcal F}), такая что:

[
\mathcal F(A_q)
===============

c_{\mathcal F}F F^\sharp,
]

[
\mathcal F(A_p)
===============

c_{\mathcal F}G G^\sharp.
]

Из вещественности и чётности:

[
F^\sharp=F,
\qquad
G^\sharp=G.
]

Следовательно:

[
\mathcal F(A_q)=c_{\mathcal F}F^2,
\qquad
\mathcal F(A_p)=c_{\mathcal F}G^2.
]

Из (A_p=A_q):

[
F^2=G^2
]

как целые функции. Поэтому:

[
(F-G)(F+G)\equiv0.
]

Кольцо целых функций не имеет делителей нуля, значит:

[
F\equiv G
\quad\text{или}\quad
F\equiv-G.
]

По инъективности Fourier transform:

[
p=q
\quad\text{или}\quad
p=-q.
]

Ненулевой линейный якорь выбирает знак. (\square)

---

# 2. Третьего класса двойников нет

Все классические phase-retrieval ambiguities убиваются точными гипотезами:

```text
translation:
  убита чётностью относительно фиксированного центра;

reflection:
  тривиальна, поскольку q(-u)=q(u);

global phase:
  вещественность сокращает её до ±1;

zero flipping:
  невозможно, поскольку F и G вещественны на real axis,
  значит |F|²=|G|² превращается в F²=G²;

piecewise sign changes across real zeros:
  несовместимы с целостью — знак не может переключаться локально;

homometric pairs:
  возможны для общих real sources, но не в real-even-entire классе.
```

Поэтому твоя интуиция верна: контрпримеры прежних раундов действительно ломали хотя бы одну из гипотез, прежде всего чётность.

Но есть три важные границы теоремы:

1. нужна **полная** автокорреляция, не только (|t|\le T);
2. нужна аналитичность преобразования — у нас она приходит из compact support;
3. якорь обязан быть линейным и ненулевым.

Если известна только локальная часть (A), можно разнести симметричные bump-компоненты на большие расстояния: их малые лаги совпадут, а источники будут разными.

---

# 3. Шаг 2: целое продолжение (FF^\sharp) из (A)

Твой шаг корректен при четырёх точных условиях.

Пусть:

[
\operatorname{supp}q
\subset[-R,R].
]

Тогда:

[
q\in L^1\cap L^2,
]

а

[
A_q=q*\widetilde q
]

удовлетворяет:

[
A_q\in L^1,
\qquad
\operatorname{supp}A_q
\subset[-2R,2R].
]

Поэтому:

[
\widehat A_q(z)
]

имеет целое продолжение экспоненциального типа не более (2R).

Точно:

[
\boxed{
\widehat A_q(z)
===============

c_{\mathcal F}F(z)F^\sharp(z).
}
]

Это можно доказать двумя способами:

* непосредственно по Fubini, поскольку все интегралы имеют компактный носитель;
* сначала на real axis через convolution theorem, затем продолжить целиком по identity theorem.

## Что обязательно пришпилить

```text
1. full zero-extension q;
2. exact support interval;
3. Fourier/Mellin sign;
4. convolution normalization c_F;
5. exact sharp involution;
6. equality A_q = q * q_tilde on all real lags.
```

Если используется unitary Fourier transform, обычно появляется множитель порядка (\sqrt{2\pi}). Если используется nonunitary transform, множителя может не быть. Для uniqueness его значение несущественно, но в theorem оно должно стоять точно.

## Стоп-код

```text
SOFT_L2_FULL_AUTOCORRELATION_OR_NORMALIZATION_GAP
```

---

# 4. Твой square-root route: где он требует ремонта

Для **инъективности** square-root construction вообще не нужен. Доказательство через:

[
F^2=G^2
]

короче и сильнее.

Но если ты хочешь утверждать более сильное:

> из одного (A) можно конструктивно восстановить (q),

тогда монодромия и Paley–Wiener действительно входят.

Обозначим:

[
H(z):=
c_{\mathcal F}^{-1}\widehat A(z).
]

Нужно построить:

[
F^2=H.
]

## 4.1 Просто односвязности (\mathbb C) недостаточно

Корень продолжается сначала на:

[
\mathbb C\setminus Z(H),
]

а эта область обычно не односвязна.

Монодромия вокруг нуля (z_0) равна:

[
(-1)^{\operatorname{ord}_{z_0}H}.
]

Поэтому глобальный целый квадратный корень существует тогда и только тогда, когда:

[
\boxed{
\operatorname{ord}_{z_0}H
\ \text{чётна для каждого нуля }z_0.
}
]

Именно чётность всех комплексных кратностей убивает монодромию.

Фраза должна быть:

> все нули (H), включая невещественные, имеют чётную кратность; тогда локальные корни склеиваются в глобальный целый корень.

---

## 4.2 Особая кратность в нуле

Если требуется не просто произвольный root, а **чётный** root (F), то в нуле нужно больше.

Поскольку (F) чётна, её порядок нуля в (0) чётен:

[
\operatorname{ord}_0F\in2\mathbb N.
]

Следовательно:

[
\boxed{
\operatorname{ord}_0H
=====================

2\operatorname{ord}_0F
\in4\mathbb N.
}
]

То есть «чётная кратность (H) в нуле» недостаточна.

Контрпример:

[
H(z)=z^2.
]

Все нули (H) имеют чётную кратность, и целые корни существуют:

[
F(z)=\pm z.
]

Но оба корня нечётны. Чётного source-transform нет.

Правильный parity guard:

```text
if H(0) ≠ 0:
  parity obstruction absent;

if H(0) = 0:
  ord_0(H) must be divisible by 4.
```

Это наиболее существенная недостающая строка твоего шага 4.

---

## 4.3 Положительность на вещественной оси

Чтобы root соответствовал вещественному источнику, нужно:

[
H(x)\ge0
\qquad(x\in\mathbb R).
]

Тогда можно выбрать вещественную ветвь (F(x)) на real axis.

Если (H) только real-valued, но отрицательна на интервале, root будет чисто мнимой там, и восстановленный источник не будет real-even в требуемом смысле.

Для истинной автокорреляции:

[
H(x)=|F(x)|^2\ge0
]

автоматически.

Но из произвольной even compact-support функции (A) это не следует. Нужна positive-definiteness либо точная autocorrelation provenance.

---

## 4.4 Рост корня

Если:

[
|H(z)|
\le
C(1+|z|)^N e^{2R|\Im z|},
]

то для целого root:

[
|F(z)|
======

|H(z)|^{1/2}
\le
C^{1/2}(1+|z|)^{N/2}e^{R|\Im z|}.
]

Значит (F) имеет вдвое меньший exponential type.

Но для восстановления (q\in L^2) также нужно:

[
F|_{\mathbb R}\in L^2.
]

Это следует, если:

[
H|_{\mathbb R}\in L^1,
]

поскольку:

[
\int_{\mathbb R}|F(x)|^2dx
==========================

\int_{\mathbb R}H(x),dx.
]

После этого Paley–Wiener даёт:

[
\operatorname{supp}q\subset[-R,R].
]

## Минимальный reconstruction contract

```text
H entire;
H not identically zero;
H(x) ≥ 0 on R;
H|R ∈ L¹;
type(H) ≤ 2R;
all zeros of H have even multiplicity;
ord_0(H) ∈ 4N if an even root is required.
```

Тогда существуют ровно два admissible root-а:

[
F,\ -F,
]

и якорь выбирает один.

---

# 5. Почему even-zero condition не получается из одного (A)

Это реальная, а не техническая гипотеза.

Рассмотрим:

[
H(z)
====

(z^2+1)
\left(\frac{\sin z}{z}\right)^4.
]

Тогда:

* (H) целая;
* (H(x)\ge0) на (\mathbb R);
* (H|_{\mathbb R}\in L^1);
* (H) имеет конечный exponential type;
* её inverse Fourier transform — real-even compactly supported positive-definite объект.

Но (H) имеет простые нули:

[
z=\pm i.
]

Следовательно, глобального целого квадратного корня нет.

Значит утверждение:

```text
compact support + positive-definiteness
→ compactly supported spectral square root
```

ложно.

В твоём проекте это не проблема, если (A) уже доказанно происходит от существующего canonical (q). Тогда:

[
H=F^2
]

и even-zero property следует из существования (q).

Но это означает:

* как theorem **уникальности** доказательство чистое;
* как theorem **существования по одному (A)** нужен отдельный even-zero certificate.

---

# 6. O2: half-shift и recentering

Здесь claim проходит только при точном intertwining theorem.

В centered Mellin-переменной (w) естественная инволюция имеет вид:

[
F^{\sharp_M}(w)
===============

\overline{F(-\bar w)}.
]

После поворота в ZEO-переменную, например:

[
G(z):=F(iz),
]

инволюция становится:

[
G^{\sharp_Z}(z)
===============

\overline{G(\bar z)}.
]

Для вещественного чётного (q):

[
F^{\sharp_M}=F,
]

и эквивалентно:

[
G^{\sharp_Z}=G.
]

То есть сам half-shift/recentering лемму не разрушает. Но нельзя переносить формулу (\sharp) из одной координаты в другую без conjugation.

## Минимальная source-locked строка

Нужен exact intertwiner:

[
\boxed{
\kappa_m\Gamma_m
================

J\kappa_m,
}
]

где:

* (\Gamma_m) — multiplicative inversion/parity на исходном carrier;
* (Jq(u)=q(-u)) — обычное отражение в centered log-coordinate.

И затем:

[
\boxed{
\mathcal T(Jq)=
(\mathcal Tq)^\sharp.
}
]

После этих двух строк:

[
q\ \text{real-even}
\Longrightarrow
F^\sharp=F.
]

Если после half-shift остаётся известный zero-free unit (u(z)), например:

[
F^\sharp=uF,
]

то theorem можно починить:

[
FF^\sharp=uF^2,
]

после чего сначала делится на source-locked (u). Но (u) нельзя придумывать post hoc.

---

# 7. Главный архитектурный guard: не спрятан ли H2a

Абстрактная лемма H2a не использует.

Но проектная инстанциация будет H2a-независимой только если утверждение:

[
q_{m,N}\in E^+*{m,N},
\qquad
q*{m,N}\ \text{real},
]

получено **по определению или отдельным upstream theorem**, а не из простоты ground state.

Если reasoning такой:

```text
operator commutes with parity
+ smallest eigenvalue simple
→ its eigenvector is even
```

то ты уже использовал содержание H2a.

Поэтому нужен один точный provenance verdict:

```text
EVEN_BY_CONSTRUCTION:
  q is selected inside the exact even-real carrier before H2a;

or

EVEN_FROM_SIMPLE_GROUND:
  parity depends on H2a and the claimed independence is false.
```

И ещё важнее: source determination не равно spectral simplicity.

Твоя лемма доказывает:

[
A_p=A_q
\Longrightarrow
p=\pm q.
]

Чтобы из неё получить простоту ground eigenspace, нужен отдельный crosswalk:

[
\boxed{
\text{каждый нормированный ground vector}
\Longrightarrow
\text{одна и та же полная автокорреляция }A.
}
]

Без этого два разных ground vectors могут иметь разные автокорреляции, и injectivity theorem к ним неприменима.

Это текущая минимальная дополнительная лемма:

[
\boxed{
\texttt{GroundEigenspaceToCanonicalAutocorrelation}.
}
]

---

# 8. Сверка двух proof-каналов

## Канал V2 — square-root reconstruction

```text
A
→ entire H = Fourier(A)
→ even-zero multiplicities
→ global square root ±F
→ inverse transform ±q
→ anchor
```

Плюсы:

* конструктивно восстанавливает источник;
* явно показывает monodromy и Paley–Wiener requirements.

Минусы:

* требует even-zero certificate;
* требует отдельного разбора порядка нуля в (0);
* сильнее, чем необходимо для uniqueness.

## Канал прошлого раунда — difference of squares

```text
A_p = A_q
→ F_p² = F_q²
→ (F_p−F_q)(F_p+F_q)=0
→ p=±q
→ anchor
```

Плюсы:

* не требует анализа нулей;
* не требует global square-root existence theorem;
* не требует real-zero property;
* минимальный и самый надёжный.

Минус:

* это theorem инъективности, а не construction from arbitrary (A).

## Вердикт сверки

Расхождения нет.

Каналы согласуются, но решают немного разные задачи:

[
\boxed{
\text{difference-of-squares — основной proof uniqueness;}
}
]

[
\boxed{
\text{square-root route — дополнительный reconstruction theorem.}
}
]

---

# FINAL PROPOSAL

Заморозить две отдельные леммы.

## 1. Основная

```text
SOFT_L2_EvenRealFullAutocorrelationRigidity

Inputs:
  real q,p;
  even q,p;
  compact support / entire transforms;
  exact full autocorrelation equality;
  same transform/sharp convention.

Output:
  p = q or p = -q.

With nonzero linear anchor:
  p = q.
```

Success code:

```text
SOFT_L2_SOURCE_INJECTIVITY_LOCKED
```

## 2. Дополнительная

```text
SOFT_L2_AutocorrelationSquareRootReconstruction

Inputs:
  H = c_F^(-1) Fourier(A);
  H ≥ 0 on R;
  H|R ∈ L¹;
  finite exponential type;
  all complex zeros even;
  ord_0(H) divisible by 4 for even source.

Output:
  exactly two compactly supported real-even roots ±q.
```

Success code:

```text
SOFT_L2_GLOBAL_ROOT_RECONSTRUCTION_LOCKED
```

## Остаточный project gap

```text
SOFT_L2_GROUND_TO_CANONICAL_A_CROSSWALK
```

Именно он решает, закрывает ли твоя лемма только source determination или действительно часть `H2a`.

# STRONGEST ATTACK

Самое сильное возражение теперь:

> Вы доказали, что один и тот же (A) не имеет двух real-even источников. Где доказательство, что все ground vectors порождают один и тот же (A)?

Если такого theorem нет, `H2a` не закрыт.

# META CLOSEOUT

**Что доказано?**

[
\boxed{
(A,\ \text{real},\ \text{even},\ \text{nonzero anchor})
\text{ определяют }q\text{ однозначно}.
}
]

**Что оказалось лишним?**

```text
все нули F вещественны;
H2b;
zero-flipping analysis внутри real-even class.
```

**Что надо исправить в V2?**

```text
all complex zero multiplicities even;
ord_0(H) ∈ 4N for even root;
Paley–Wiener L² condition;
exact half-shift/sharp intertwiner.
```

**Текущий самый маленький gap:**

[
\boxed{
\texttt{GroundEigenspaceToCanonicalAutocorrelation}.
}
]

**Progress class:** `PROOF_PROGRESS`.
