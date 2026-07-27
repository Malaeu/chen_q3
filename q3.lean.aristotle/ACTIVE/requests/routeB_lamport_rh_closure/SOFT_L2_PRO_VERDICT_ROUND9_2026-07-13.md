STATUS: REFUTED AS STATED — механизм следующего порядка остаётся условно жив

Главный вердикт:

Текущее лаг-уравнение:
  неполно типизировано, пока E_j^bdry не разложен точно.

Однородное предельное уравнение:
  действительно вырождается, если A_Φ является его решением.

“Первый порядок”:
  не гарантирован; первый ненулевой порядок может быть вторым или выше.

Единственность:
  normalized positive-definite + even + subexponential недостаточно.

RH:
  NOT_RH.

Проект уже работает с операторами как точными сжатиями, а не с неформальными «ограничениями»; кроме того, текущий audit требует сохранять pole/edge/cross terms явно. Поэтому без полного projection ledger обозначение E
j
bdry
	​

 пока может скрывать всю трудность. 

RH_Q3

 

Факторизация Defect Gram Bridge

1. Точное лаг-уравнение: какие члены могут быть потеряны

Пусть

I
L
	​

=[−L/2,L/2],P
L
	​

=1
I
L
	​

	​

,Q
L
	​

=I−P
L
	​

,

а

(U
a
	​

f)(u)=f(u−a).

Пусть q
j
	​

 нормирован и продолжен нулём вне I
L
j
	​

	​

. Определим

A
j
	​

(t):=⟨U
t
	​

q
j
	​

,q
j
	​

⟩.
1.1 Сначала общий операторный ledger

Пусть S
j
	​

 — полная конечная проекция, включающая всё, что реально присутствует:

window projection;
Galerkin projection E_(m,N);
parity sector;
другие source-locked finite projections.

Пусть полный translation-invariant объект до сжатия равен

T
j
full
	​

=A
j
	​

−
n
∑
	​

w
n
	​

(U
ℓ
n
	​

	​

+U
−ℓ
n
	​

	​

),w
n
	​

=
n
	​

Λ(n)
	​

,ℓ
n
	​

=logn.

Пусть конечный оператор имеет точную форму

M
j
	​

=S
j
	​

T
j
full
	​

S
j
	​

+C
j
corr
	​

,

где C
j
corr
	​

 содержит pole, midpoint и другие явные поправки.

Если

M
j
	​

q
j
	​

=μ
j
	​

q
j
	​

,S
j
	​

q
j
	​

=q
j
	​

,

то тестирование против S
j
	​

U
t
	​

q
j
	​

 даёт точно

⟨U
t
	​

q
j
	​

,T
j
full
	​

q
j
	​

⟩=μ
j
	​

A
j
	​

(t)+E
j
proj
	​

(t)+E
j
corr
	​

(t),
	​


где

E
j
proj
	​

(t)=⟨(I−S
j
	​

)U
t
	​

q
j
	​

,T
j
full
	​

q
j
	​

⟩,
	​


и, при знаке +C
j
corr
	​

 в M
j
	​

,

E
j
corr
	​

(t)=−⟨S
j
	​

U
t
	​

q
j
	​

,C
j
corr
	​

q
j
	​

⟩.
	​


Это правильный master-ledger.

Если конечный carrier содержит Galerkin-проекцию, то E
j
proj
	​

 не является чисто граничным членом. Он содержит также:

E
j
Gal
	​

(t)∼⟨(I−Π
N
j
	​

	​

)P
L
j
	​

	​

U
t
	​

q
j
	​

,P
L
j
	​

	​

T
j
full
	​

q
j
	​

⟩.
	​


У него обычно нет компактного носителя по t.

Поэтому текущее имя

E
j
bdry
	​


допустимо только после theorem:

GALERKIN_PROJECTION_DEFECT_ZERO

или после явного разложения

E
j
proj
	​

=E
j
win
	​

+E
j
Gal
	​

+E
j
sector
	​

.
1.2 Оконная часть для prime shifts

Если временно S
j
	​

=P
L
	​

, то для одного сдвига:

⟨P
L
	​

U
t
	​

q,P
L
	​

U
a
	​

q⟩
	​

=⟨U
t
	​

q,U
a
	​

q⟩−⟨Q
L
	​

U
t
	​

q,U
a
	​

q⟩
=A(t−a)−D
a,L
	​

(t),
	​


где

D
a,L
	​

(t)=⟨Q
L
	​

U
t
	​

q,Q
L
	​

U
a
	​

q⟩.
	​


Следовательно, точный prime-boundary defect:

E
P,L
win
	​

(t)=−
n
∑
	​

w
n
	​

[D
ℓ
n
	​

,L
	​

(t)+D
−ℓ
n
	​

,L
	​

(t)]
	​


с учётом общего знака после переноса в правую часть.

Носитель

Для симметричного интервала:

D
a,L
	​

(t)

=0⟹ta>0и∣t−a∣<L.
	​


То есть prime-boundary defect не локализован только около ∣t∣≈L.

Для фиксированного a>0 он потенциально ненулевой для всех малых t>0. Это уже опровергает возможную фразу:

«boundary source живёт только на дальних лагах».

1.3 Точная boundary-mass шкала

Определим

r
L
	​

(a):=∥Q
L
	​

U
a
	​

q∥
2
	​

.

Для 0<a<L:

r
L
	​

(a)
2
=∫
L/2−a
L/2
	​

∣q(u)∣
2
du.

Для −L<a<0:

r
L
	​

(a)
2
=∫
−L/2
−L/2−a
	​

∣q(u)∣
2
du.

По Коши–Шварцу:

∣D
a,L
	​

(t)∣≤r
L
	​

(t)r
L
	​

(a).
	​


Поэтому на компакте ∣t∣≤T:

∣E
P,L
win
	​

(t)∣≤r
L
	​

(t)
n
∑
	​

w
n
	​

(r
L
	​

(ℓ
n
	​

)+r
L
	​

(−ℓ
n
	​

)).
	​


Без отдельной оценки на boundary mass это не малый член.

Если cutoff имеет вид

ℓ
n
	​

≤L⟺n≤e
L
,

то даже грубо:

n≤e
L
∑
	​

n
	​

Λ(n)
	​

≤
n≤e
L
∑
	​

n
	​

logn
	​

≲Le
L/2
.

Значит componentwise-оценка требует примерно

r
L
	​

(t)≪
L
e
−L/2
	​

,

либо должна использоваться точная combined cancellation.

Из нормировки ∥q∥
2
	​

=1 такая малость не следует.

1.4 Архимедова compression defect

Если A
L
	​

 — полный Arch-оператор, то

⟨P
L
	​

U
t
	​

q,P
L
	​

A
L
	​

q⟩=⟨U
t
	​

q,A
L
	​

q⟩−D
Arch,L
	​

(t),

где

D
Arch,L
	​

(t)=⟨Q
L
	​

U
t
	​

q,A
L
	​

q⟩.
	​


Если Arch-оператор действительно имеет convolution kernel, первый член равен

(K
Arch,L
	​

⋆A)(t)

с точным D0.6-знаком.

Оценка:

∣D
Arch,L
	​

(t)∣≤r
L
	​

(t)∥Q
L
	​

A
L
	​

q∥
2
	​

.
	​


Если K
Arch
	​

 нелокален, этот defect в общем случае не имеет компактного носителя по t.

Если Arch — только distributional multiplier, то буквальная запись K
Arch
	​

⋆A требует отдельного domain theorem.

1.5 Исправленная формула

После фиксации знаков:

(A
j
	​

A
j
	​

)(t)−
n
∑
	​

w
n
	​

[A
j
	​

(t−ℓ
n
	​

)+A
j
	​

(t+ℓ
n
	​

)]=μ
j
	​

A
j
	​

(t)+E
j
proj
	​

(t)+E
j
corr
	​

(t).
	​


Не следует заранее называть всё справа bdry.

Первый verdict
SOFT_L2_LAG_EQUATION_LEDGER_INCOMPLETE

пока не разложены:

window commutator;
Galerkin/finite-carrier defect;
parity projection defect;
Arch truncation defect;
pole/midpoint correction;
source sign and normalization.
2. Вырожденность предельного уравнения
2.1 Наблюдение о Reξ
′
/ξ

Пусть

Ξ(x)=ξ(1/2+ix).

На вещественной оси Ξ(x) вещественна. Вне её нулей:

Ξ(x)
Ξ
′
(x)
	​

=i
ξ
ξ
′
	​

(1/2+ix)∈R.

Поэтому:

Re
ξ
ξ
′
	​

(1/2+ix)=0
	​


вне нулей, без RH.

Но это ещё не доказывает, что exact operator symbol стремится к нулю в нужной topology.

Особенно важно различать:

Re
ξ
ξ
′
	​

	​

ℜs=1/2
	​


и односторонний предел

ε↓0
lim
	​

Re
ξ
ξ
′
	​

(1/2+ε+ix).

Второй объект может содержать singular zero-measure information.

2.2 Абстрактный тест подтверждает вырожденность

Пусть Fourier multiplier лаг-оператора после вычитания eigenvalue равен

ℓ
j
	​

(x).

Пусть Bochner measure автокорреляции:

dν
j
	​

(x)=c
F
	​

∣F
j
	​

(x)∣
2
dx.

Лаг-уравнение в Fourier-side имеет форму

ℓ
j
	​

dν
j
	​

=d
E
j
	​

.
	​


Предположим, что:

ℓ
j
	​

→ℓ
∞
	​

,
E
j
	​

→0,ν
j
	​

→ν
Φ
	​

,

где

dν
Φ
	​

=c∣Ξ(x)γ
0
	​

(x)∣
2
dx.

Поскольку Ξγ
0
	​

 — ненулевая голоморфная функция, её нули дискретны. Поэтому плотность ν
Φ
	​

 положительна почти всюду.

Если A
Φ
	​

 решает однородное уравнение, то:

ℓ
∞
	​

(x)∣Ξ(x)γ
0
	​

(x)∣
2
=0почти всюду.

Следовательно:

ℓ
∞
	​

=0почти всюду.
	​


То есть:

однородное предельное уравнение действительно не может дать единственность.
	​


Это подтверждает твою зарегистрированную гипотезу, причём без необходимости заранее идентифицировать символ с Reξ
′
/ξ.

2.3 Но «следующий порядок» может быть не первым

Пусть ε
j
	​

↓0 — source-derived scale.

Нужно найти первый ненулевой порядок r≥1, для которого:

ε
j
−r
	​

ℓ
j
	​

⟶ℓ
(r)

и

ε
j
−r
	​

E
j
	​

⟶S
(r)
.

Тогда правильное уравнение:

ℓ
(r)
dν=dS
(r)
.
	​


В lag-side:

L
(r)
A=S
bdry
(r)
	​

.
	​


Нельзя заранее регистрировать r=1.

Почему zero-measure может всё ещё ничего не видеть

Если первый scaled multiplier даёт только:

ℓ
(1)
=
γ
∑
	​

c
γ
	​

δ
γ
	​

,

то

δ
γ
	​

⋅∣Ξ∣
2
=∣Ξ(γ)∣
2
δ
γ
	​

=0.

Для простого нуля ∣Ξ∣
2
 имеет нуль второго порядка, поэтому даже:

δ
γ
′
	​

⋅∣Ξ∣
2
=0.

Лишь производные достаточно высокого порядка потенциально видят curvature.

Следовательно:

«zero-counting measure появляется на первом порядке»

⇒идентификация A
Φ
	​

.
	​


Информация может находиться на втором или более высоком порядке.

2.4 Главная новая стена: source closure

Даже правильное scaled equation бесполезно, если

S
bdry
(r)
	​


зависит от скрытых boundary traces q
j
	​

, а не только от A
j
	​

.

Автокорреляция инвариантна при сдвиге:

q
j
	​

(u)↦q
j
	​

(u−a)⟹A
j
	​

(t) не меняется.

Но при фиксированном окне boundary defect меняется.

Следовательно, возможны два q с одинаковым A, но разными E
bdry
.

Тогда уравнение не замкнуто на A.

Нужен отдельный theorem:

BoundarySourceClosureCrosswalk
	​


утверждающий одно из:

boundary source исчезает на scaled уровне;

construction gauge фиксирует его однозначно;

scaled source выражается только через A;

source имеет независимо заданный target-limit.

Иначе:

SOFT_L2_BOUNDARY_NOT_CLOSED_ON_AUTOCORRELATION
3. Класс единственности

Нормированные положительно-определённые функции имеют представление Бохнера:

A(t)=∫
R
	​

e
itx
dν(x),

где ν — вероятностная мера.

Если A вещественна и чётна, ν симметрична.

Но этого недостаточно.

Для любого ω:

A
ω
	​

(t)=cos(ωt)

является:

нормированной;
вещественной;
чётной;
положительно-определённой;
целой;
экспоненциального типа;
subexponential в любой более слабой формулировке.

Её мера:

ν
ω
	​

=
2
1
	​

(δ
ω
	​

+δ
−ω
	​

).
3.1 Точный uniqueness theorem

Пусть scaled Fourier equation:

ℓ(x)dν(x)=dS(x).

Обозначим:

Z
ℓ
	​

:={x:ℓ(x)=0}.

На R∖Z
ℓ
	​

 мера определяется:

dν(x)=
ℓ(x)
1
	​

dS(x).

На Z
ℓ
	​

 уравнение ничего не видит.

Поэтому минимальный класс:

C
ℓ,S
	​

={A=
ν
:
	​

ν≥0,ν(R)=1,ν симметрична,
ℓν=S,ν(Z
ℓ
	​

)=0}.
	​

	​


Если:

ℓ
1
	​

S

является конечной положительной вероятностной мерой, то решение в этом классе единственно.

Альтернативы условию ν(Z
ℓ
	​

)=0

Достаточно любого из:

ell(x) ≠ 0 для всех real x;

ν абсолютно непрерывна, а Z_ell имеет меру Лебега 0;

support(ν) заранее отделён от Z_ell;

дополнительные независимые equations фиксируют массу на Z_ell.
3.2 Как исключается контрпример двух косинусов

Если:

ℓ(±ω)=0,S=0,

то:

ν
ω
	​

=
2
1
	​

(δ
ω
	​

+δ
−ω
	​

)

решает уравнение.

Чтобы исключить его, недостаточно:

evenness;
entire;
subexponential;
compact spectral support;
normalization.

Нужно исключить mass на Z
ℓ
	​

.

Самый естественный проектный guard:

ν≪dx
	​


вместе с:

∣Z
ℓ
	​

∣
Leb
	​

=0.

S1/local-normal-family может помочь: если cluster point действительно имеет форму

dν=∣F(x)∣
2
dx,

то атомарные cosine-solutions исключены.

Если Z
ℓ
	​

 содержит интервал, даже абсолютная непрерывность не спасает: uniqueness снова невозможна.

Сдвиговый plant
Для exact lag equation

Сдвигаем q внутри фиксированного окна:

q(u)↦q(u−a).

Автокорреляция не меняется, но boundary source меняется.

Ожидание:

raw boundary formula changes;
A-side remains unchanged.

Если proposed E
bdry
 не реагирует:

SOFT_L2_WINDOW_SHIFT_COMMUTATOR_MISSING

Если сдвигаем одновременно q и окно, уравнение должно быть ковариантным.

Для next-order source

Если заявляется:

S
(r)
=S
(r)
[A],

то fixed-window shift обязан либо:

быть запрещён exact gauge theorem;

либо не менять scaled source.

Иначе:

SOFT_L2_BOUNDARY_NOT_CLOSED_ON_AUTOCORRELATION
Для uniqueness class

Любое условие, использующее абсолютный центр q, незаконно как условие на A: сдвиг q не меняет A.

Условия:

ν absolutely continuous;
ν(Z_ell)=0;
ell ν=S;
A(0)=1

plant проходят.

ROUTE MAP
Exact finite eigenvector equation
        |
        v
ExactProjectionDefectLagEquation
        |
        v
window + Galerkin + correction ledger
        |
        v
homogeneous limit
        |
        +--> either A_Φ fails it → route killed
        |
        +--> or symbol flattens → equation degenerate
                         |
                         v
FirstNonzeroScaledLagEquation
                         |
                         v
BoundarySourceClosureCrosswalk
                         |
                         v
MeasureDivisionUniqueness
                         |
                         v
A = c A_Φ
FINAL PROPOSAL

Не переходить пока к PolyaAutocorrelationUniqueness.

Следующий минимальный theorem:

SOFT_L2_ExactProjectionDefectLagEquation.
	​


Он должен:

использовать полную проекцию S
m,N
	​

;

вывести

E
proj
=⟨(I−S)U
t
	​

q,T
full
q⟩;

разложить его на:

window;
Galerkin;
sector;
pole/midpoint;
Arch truncation;

доказать точный support statement для window-shift terms;

дать same-unit bounds через r
L
	​

(t);

пройти оба shift plants;

не утверждать малость.

Только после этого:

SOFT_L2_FirstNonzeroFlatteningEquation.
	​

STRONGEST ATTACK

Самое сильное возражение сейчас:

Ваш E
j
bdry
	​

 — это не boundary term. В нём скрыт Galerkin defect, потому что сдвинутый eigenvector не принадлежит конечному carrier.

Если это верно, заявленное лаг-уравнение пока не является closed equation для автокорреляции.

Второе:

Если A
Φ
	​

 решает homogeneous multiplier equation и его spectral density положительна почти всюду, multiplier обязан быть нулём почти всюду. Откуда тогда возьмётся uniqueness?

Только из первого ненулевого scaled equation и source.

Третье:

Даже scaled equation не уникальна, если multiplier имеет real zero set, несущий положительные меры.

Это точная форма контрпримера двух косинусов.

CODEX DIRECTIVE
TARGET:
  SOFT_L2_ExactProjectionDefectLagEquation

Inputs

exact finite carrier projection S_(m,N);
full Arch operator;
full prime shift operator;
exact correction operator;
finite ground eigenvector;
D0.6 transform/shift convention.

Forbidden

no asymptotic smallness;
no “boundary” name before decomposition;
no omission of Galerkin projection;
no RH;
no Re xi'/xi substitution for the exact symbol;
no numerical support inference.

Success code

SOFT_L2_EXACT_PROJECTION_LEDGER_LOCKED

Stop codes

SOFT_L2_WINDOW_SHIFT_COMMUTATOR_MISSING
SOFT_L2_GALERKIN_SHIFT_DEFECT_MISSING
SOFT_L2_ARCH_DOMAIN_GAP
SOFT_L2_CORRECTION_LEDGER_MISSING
SOFT_L2_BOUNDARY_SCALE_UNPROVED
SOFT_L2_SHIFT_PLANT_INERT
META CLOSEOUT

Что убито?

“Ebdry — автоматически малый край”;
однородная предельная uniqueness;
normalized p.d. + even + subexponential как достаточный класс.

Что подтверждено?

Если A
Φ
	​

 решает homogeneous limit, то этот limit вырожден.
	​


Что стало меньше?

Идентификация сжалась до:

первый ненулевой scaled multiplier+замкнутый scaled source+no-mass-on-zero-set.
	​


Текущий smallest gap:

ExactProjectionDefectLagEquation.
	​


Progress class: FALSIFICATION_PROGRESS.

Route score: 5/5. Однородная идея убита, но точная форма следующего содержательного уравнения теперь ясна.

