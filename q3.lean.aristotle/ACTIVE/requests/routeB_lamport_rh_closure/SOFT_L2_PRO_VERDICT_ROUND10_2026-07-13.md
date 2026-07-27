По документу от 12 июля 2026 года, старая карта фиксировала в D0.4 только точные parity-секторы и прямо не разрешала автоматически заключать «parity cleanliness»; D0.5 отдельно запрещал подмешивать простоту или evenness ground state без теоремы. Поэтому я принимаю твоё новое утверждение

q
m,N
	​

 вещественна и чётна

как более поздний замороженный вход, но в ledger должна стоять отдельная ссылка именно на theorem, выбирающий канонический ground vector в even-секторе, а не только на определение сектора D0.4.

STATUS: PARTIAL
Parity removes translation gauge:
  PROVED

Parity alone closes the scaled source:
  REFUTED

Full edge-profile theorem can unify source decay and S1:
  CONDITIONAL

Edge decay alone implies c > 0:
  REFUTED

Single ε_j and one order r:
  NOT YET JUSTIFIED

RH:
  NOT_RH
1. Parity-closure
1.1 Сдвиговая свобода действительно уничтожена

Пусть q

=0 компактно поддержана и чётна:

q(−u)=q(u).

Пусть её сдвиг

(U
a
	​

q)(u):=q(u−a)

тоже чётен. Тогда

q(u−a)=q(−u−a)=q(u+a).

Положив v=u−a, получаем

q(v)=q(v+2a).

То есть q периодична с периодом 2a. Ненулевая компактно поддержанная функция не может быть периодической с ненулевым периодом. Следовательно,

a=0.
	​


Итак, прежний spatial-shift plant действительно больше не admissible:

even q
+ symmetric fixed window
→ translation gauge fixed.

Это настоящий прогресс.

1.2 Остаточные свободы

Отражение не создаёт нового объекта:

q(−u)=q(u).

Глобальная фаза

q↦e
iθ
q

сохраняет автокорреляцию и любой sesquilinear quadratic source:

A
q
	​

(t)=⟨U
t
	​

q,q⟩,
E[q](t)=⟨X
t
	​

q,Yq⟩.

Оба фазовых множителя сокращаются. Знак q↦−q — тот же harmless gauge.

Но остаётся один guard: вещественная структура. Чётность комплексной функции сама по себе не исключает phase-retrieval ambiguity. Поэтому нужна точная строка:

q_(m,N) is real-valued after the canonical phase normalization.

Без неё:

SOFT_L2_REAL_STRUCTURE_MISSING
1.3 Полная автокорреляция определяет real-even q

Здесь есть полезная строгая лемма.

RealEvenAutocorrelationRigidity

Пусть q,p∈L
2
(R):

вещественны;

чётны;

компактно поддержаны;

имеют одинаковую полную автокорреляцию:

A
q
	​

(t)=A
p
	​

(t)∀t∈R.

Тогда

p=±q.

Если дополнительно зафиксирован один положительный anchor, например

q
	​

(0)>0,
p
	​

(0)>0,

то

p=q.
Доказательство

Пусть F
q
	​

,F
p
	​

 — Fourier transforms. Из real-even следует, что они вещественны на вещественной оси. По Wiener–Khinchin:

A
q
	​

	​

=∣F
q
	​

∣
2
=F
q
2
	​

,
A
p
	​

	​

=F
p
2
	​

.

Следовательно,

F
q
	​

(x)
2
=F
p
	​

(x)
2
(x∈R).

Из compact support обе функции целые, поэтому identity theorem даёт

F
q
2
	​

=F
p
2
	​


на всей комплексной плоскости. Значит

(F
q
	​

−F
p
	​

)(F
q
	​

+F
p
	​

)≡0.

Кольцо целых функций не имеет делителей нуля, поэтому

F
p
	​

=F
q
	​

илиF
p
	​

=−F
q
	​

.

После обратного преобразования:

p=±q.

□

1.4 Что это реально закрывает

Это позволяет доказать finite determinacy:

(A
q
	​

, real-even phase lock, I
L
	​

) однозначно определяют q с точностью до harmless sign.
	​


Следовательно, любой фазово-инвариантный boundary/projection source формально является функционалом полной автокорреляции:

E
L
	​

[q]=E
L
	​

[A
q
	​

].

Это квалифицируется как твой вариант 2 только на точном конечном уровне:

construction gauge fixes the source for each (m,N).

Но этого ещё недостаточно для предела.

Почему

Мы имеем только локальную сходимость:

A
j
	​

→Aв D
loc
′
	​


или на компактных лагах.

Она не контролирует информацию о q
j
	​

 около движущихся краёв

∣u∣≈L
j
	​

/2.

Полная автокорреляция каждого отдельного q
j
	​

 действительно определяет q
j
	​

, но операция

A
j
	​

↦edge profile of q
j
	​


не обязана быть непрерывной в локальной topology.

Поэтому минимальная честная формулировка такова.

BoundarySourceClosureCrosswalk

Для каждого j:

E
j
proj
	​

=E
L
j
	​

	​

(A
j
	​

,e
j
	​

),

где e
j
	​

 — explicit edge-profile datum либо topology, достаточно сильная для его восстановления.

И затем отдельно:

A
j
	​

→A,e
j
	​

→e,
ε
j
−r
	​

E
L
j
	​

	​

(A
j
	​

,e
j
	​

)⟶E
∞
(r)
	​

(A,e)

в требуемой distribution topology.

Итог:

parity closes gauge, but not source continuity.
	​


Стоп-код:

SOFT_L2_PARITY_GAUGE_LOCKED_SOURCE_CONTINUITY_OPEN
2. Edge-mass как общий корень

Определим total two-edge mass:

e
L
	​

(δ):=(∫
{L/2−δ<∣u∣≤L/2}
	​

∣q
L
	​

(u)∣
2
du)
1/2
,0≤δ≤L/2.

Удобнее эквивалентный radial tail:

M
L
	​

(R):=(∫
∣u∣≥R
	​

∣q
L
	​

(u)∣
2
du)
1/2
.

Они связаны:

M
L
	​

(R)=e
L
	​

(L/2−R).
2.1 Fixed-width edge mass недостаточна

Если доказать только

e
L
	​

(δ
0
	​

)→0

для каждого фиксированного δ
0
	​

, это не даёт GM.

Контрпример: две нормированные чётные bump-функции около

u=±L/4.

Тогда для каждого фиксированного δ
0
	​

:

e
L
	​

(δ
0
	​

)=0

при больших L, но

∫e
2η∣u∣
∣q
L
	​

(u)∣
2
du≍e
ηL/2
→∞.

То есть:

small mass at the immediate edge
≠
global exponential localization.
2.2 Минимальный настоящий объединитель

Нужна теорема на всём диапазоне глубин, а не на одном δ.

UniformRadialExponentialLocalization

Существуют

η
∗
	​

>0,C<∞

такие, что для всех L и всех

0≤R≤L/2:
M
L
	​

(R)≤Ce
−η
∗
	​

R
.
	​

(UREL)

Эквивалентно:

e
L
	​

(δ)≤Ce
−η
∗
	​

(L/2−δ)
	​

(0≤δ≤L/2).

Это уже может обслужить первые два потребителя.

2.3 UREL ⇒ GM

Для любого

0<η<η
∗
	​


имеем

∫e
2η∣u∣
∣q
L
	​

(u)∣
2
du
	​

=1+2η∫
0
∞
	​

e
2ηR
M
L
	​

(R)
2
dR
≤1+2ηC
2
∫
0
∞
	​

e
−2(η
∗
	​

−η)R
dR.
	​


Следовательно,

L
sup
	​

∫e
2η∣u∣
∣q
L
	​

(u)∣
2
du<∞.
	​

(GM)

Отсюда для каждой меньшей подполосы

∣ℑz∣≤η
′
<η

получаем

∣F
L
	​

(z)∣≤
2π(η−η
′
)
	​

∥e
η∣⋅∣
q
L
	​

∥
2
	​

	​


в unitary Fourier convention.

Следовательно:

UREL⟹GM⟹S1.
	​

2.4 UREL и window-source

Из exact projection ledger обычно получается bound формы

∣t∣≤T
sup
	​

∣E
L
win
	​

(t)∣≤e
L
	​

(T)Ω
L
	​

,

где Ω
L
	​

 — same-unit budget всех shift/Arch коэффициентов, оставшихся после exact cancellation ledger.

Предположим:

Ω
L
	​

≤C
T
	​

L
a
e
ωL
.

Тогда UREL даёт:

e
L
	​

(T)≤C
T
	​

e
−η
∗
	​

(L/2−T)
,

и поэтому

∣t∣≤T
sup
	​

∣E
L
win
	​

(t)∣≤C
T
	​

L
a
e
−(η
∗
	​

/2−ω)L
.
	​


Чтобы источник исчез после масштабирования:

ε
L
−r
	​

E
L
win
	​

→0,

необходимо:

L
a
e
−(η
∗
	​

/2−ω)L
=o(ε
L
r
	​

).
	​

(RATE)

Это точное rate condition.

Например, если exact coefficient budget имеет масштаб

Ω
L
	​

≍e
L/2
poly(L),

то ω=1/2. Для полиномиального ε
L
	​

 достаточно

η
∗
	​

>1.

Для

ε
L
	​

=e
−βL

нужно:

2
η
∗
	​

	​

−ω>βr.

Значит потребители не несовместимы в принципе, но source-channel предъявляет существенно более сильную rate demand, чем S1.

2.5 Edge decay не даёт c>0 сама по себе

Даже сильнейший spatial decay не запрещает spectral mass уходить из фиксированного I.

Возьмём фиксированную real-even rapidly decaying q и

q
j
	​

(u)=C
j
	​

q(u)cos(β
j
	​

u),β
j
	​

→∞.

Все q
j
	​

 имеют одинаково хороший spatial decay, но их Fourier mass уходит к

±β
j
	​

.

Для любого фиксированного интервала I:

∫
I
	​

∣F
j
	​

(x)∣
2
dx→0.

То есть product-limit scale может быть:

c=0.

Поэтому:

UREL alone does not imply c>0.
	​


Но UREL даёт S1. А уже замороженная логика:

S1+F
j
	​

(i/4)=A
∗
	​


=0+∣F
j
	​

∣
2
→c∣T∣
2

даёт:

c>0.

Таким образом, единая честная цепочка:

UREL⇒{
scaled window-source decay,
GM/S1,
	​

	​


и затем

S1 + fixed anchor + product identification⇒c>0.
	​


Anchor не может быть удалён из theorem.

Итог по edge-mass
Fixed-width e_L(δ):
  insufficient.

All-depth exponential profile:
  can unify source decay and S1.

c > 0:
  requires anchor/frequency-gauge input in addition.

Стоп-коды:

SOFT_EDGE_FIXED_WIDTH_INSUFFICIENT
SOFT_EDGE_RATE_INCOMPATIBLE
SOFT_C_ANCHOR_MISSING
3. Шкала ε
j
	​

 и порядок r
3.1 μ
j
	​


Raw eigenvalue

μ
j
	​


обычно незаконна как scale.

Причина: при замене

M
j
	​

↦M
j
	​

+c
j
	​

I

ground vector и автокорреляция не меняются, но

μ
j
	​

↦μ
j
	​

+c
j
	​

.

Поэтому μ
j
	​

 не gauge-invariant.

Легален только centred defect:

δμ
j
	​

=μ
j
	​

−c
j
flat
	​

,
	​


где c
j
flat
	​

 — source-locked flattening level symbol/operator и доказано:

δμ
j
	​

→0.

Иными словами:

μ_j:
  illegal raw.

μ_j − exact flattening constant:
  potentially legal.
3.2 1/L
j
	​

ε
j
	​

=
L
j
	​

1
	​


— законный кандидат, потому что L
j
	​

 является construction parameter.

Но он становится theorem scale только после exact expansion:

ℓ
j
	​

=L
j
−1
	​

ℓ
(1)
+L
j
−2
	​

ℓ
(2)
+⋯

и соответствующего source expansion.

Hard-window defects могут быть:

O(1/L);

exponential;

oscillatory;

edge-mass dominated.

Поэтому выбирать 1/L по аналогии с Toeplitz/Widom нельзя.

3.3 Edge mass

Edge mass — законная source-derived scale:

ε
j
	​

=e
L
j
	​

	​

(T
0
	​

)

или global profile coefficient.

Но она контролирует source, не обязательно multiplier flattening.

Кроме того, exact window term

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

q⟩

содержит два edge factors. Поэтому при ε=e
L
	​

:

D
a,L
	​

=O(ε
2
).

То есть чистый window-shift defect естественно имеет degree 2.

Но другие master-ledger terms могут быть линейными:

⟨Q
L
	​

U
t
	​

q,A
L
	​

q⟩,

Galerkin defect, pole/correction coordinates и так далее.

Следовательно:

parity does not force r=2.
	​


Parity связывает левый и правый края. Во многих формулах они складываются, а не сокращаются.

3.4 Возможно, одного ε
j
	​

 вообще нет

Реальная система может иметь независимые scales:

h
j
	​

=
L
j
	​

1
	​

,g
j
	​

=e
L
j
	​

	​

(T),d
j
	​

=δμ
j
	​

.

Тогда expansion имеет вид:

ℓ
j
	​

=h
j
	​

ℓ
10
	​

+g
j
	​

ℓ
01
	​

+h
j
2
	​

ℓ
20
	​

+h
j
	​

g
j
	​

ℓ
11
	​

+⋯.

Нельзя назначать один порядок r, пока не доказано соотношение:

g
j
	​

≍h
j
α
	​

,d
j
	​

≍h
j
β
	​


вдоль exact admissible sequence.

Правильный инструмент — valuation/Newton ledger:

term
primitive scale
power
units
parity
target visibility

Если ни одна scale не доминирует:

SOFT_L2_MULTISCALE_NO_DOMINANT_PARAMETER
4. Самый дешёвый тест r=1 против r=2

Нужен не fit и не ratio по нескольким клеткам.

Нужен:

FirstVariationAndVisibilityAudit.
	​


Он имеет два слоя.

Слой A — algebraic edge degree

Каждому factor вида

Q
L
	​

U
a
	​

q

присваиваем degree 1.

Затем расширяем каждый exact master-ledger term.

Если существует незанулённый degree-1 term:

r
algebraic
	​

=1.

Если все exact terms имеют degree ≥2:

r
algebraic
	​

≥2.

Для чистого window overlap:

⟨Q
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

q⟩

degree равен 2.

Для mixed Arch/Galerkin term может быть 1.

Это решается до любого предельного анализа.

Слой B — target visibility

Даже если первый coefficient ненулевой:

ℓ
j
	​

=ε
j
	​

ℓ
(1)
+o(ε
j
	​

),

он может быть невидим на target:

ℓ
(1)
dν
Φ
	​

=0.

Особенно если ℓ
(1)
 поддержан на нулях Ξ.

Для простого нуля γ:

∣Ξ(x)∣
2

имеет нуль порядка 2. Поэтому:

δ
γ
	​

∣Ξ∣
2
=0,
δ
γ
′
	​

∣Ξ∣
2
=0.

Первый algebraic order может существовать, но не нести идентификационной информации.

Нужно различать:

r
algebraic
	​


и

r
informative
	​

.
Три возможных исхода
1. First coefficient nonzero and visible:
   r_algebraic = r_informative = 1.

2. First coefficient identically zero:
   r_algebraic ≥ 2.

3. First coefficient nonzero but annihilates ν_Φ:
   r_algebraic = 1,
   r_informative ≥ 2.
Точный дешёвый судья

Вычислить только first variation:

ℓ
(1)
,S
(1)
,

и проверить distribution identity:

ℓ
(1)
dν
Φ
	​

=
?
dS
(1)
.
	​


Один тест χ, на котором разность ненулевая, доказывает informative r=1.

Чтобы доказать r≥2, нужна символическая тождественная отмена для всех χ, а не ноль в одной точке.

Если обе стороны ненулевые, но совпадают вырожденным zero-supported образом, переходить ко второму порядку.

Численный Richardson ratio может быть только диагностикой.

STRONGEST ATTACK

Самое сильное возражение к parity repair:

Вы убрали spatial shift, но почему local convergence автокорреляций контролирует edge profile у движущейся границы?

Не контролирует. Это всё ещё отдельная theorem.

Самое сильное возражение к edge unifier:

Почему малость одной полоски около края должна запрещать mass около L/4?

Не должна. Нужен all-depth tail profile.

Самое сильное возражение к одному r:

У вас bulk flattening может идти как 1/L, а source как e
L
2
	​

. Почему это вообще одна asymptotic scale?

Пока причины нет.

FINAL PROPOSAL

Следующий минимальный лист:

SOFT_L2_ProjectionDefectDegreeAndScaleAudit.
	​


Он должен для каждого exact source term записать:

term name
window / Galerkin / Arch / correction
parity
real/complex status
number of edge factors
primitive scale
units
first-variation coefficient
visibility on |Xi|²
Success code
SOFT_L2_SCALE_AND_DEGREE_LEDGER_LOCKED
Stop codes
SOFT_L2_REAL_EVEN_PHASE_LOCK_MISSING
SOFT_L2_SOURCE_NOT_CONTINUOUS_IN_LOCAL_A
SOFT_EDGE_PROFILE_TOO_WEAK
SOFT_EDGE_RATE_INCOMPATIBLE
SOFT_L2_MULTISCALE_NO_DOMINANT_PARAMETER
SOFT_L2_FIRST_ORDER_TARGET_INVISIBLE
META CLOSEOUT

Что закрыла parity?

translation gauge and left/right duplication.
	​


Что она не закрыла?

continuity of the moving-edge source from local A.
	​


Какой единый decay theorem возможен?

M
L
	​

(R)≤Ce
−η
∗
	​

R
	​


на всём диапазоне R, плюс rate compatibility и fixed anchor.

Что теперь означает r?

Не одно число до аудита. Надо различать:

r
algebraic
	​

иr
informative
	​

.
	​


Следующий дешёвый decisive test:

посчитать exact edge-degree и первый variation каждого уже выведенного projection-source term. Это решит r=1 против r=2 раньше любой тяжёлой предельной теоремы.

