Worked for 21m 16s

# STATUS: OPEN — обе цели строго сжаты



```
LEMMA A:
  REDUCED_TO(HlambdaOuterLobeGate)

LEMMA B:
  REDUCED_TO(FiniteCoreThetaOrderWithTailBudget)

KILLED:
  neither lemma

PAPER_PROVED:
  the two reduction theorems below
```

Численные результаты 022/024 нигде в доказательствах не используются. Они только объясняют, почему дальнейшая десятичная эскалация остановлена: после $p_{\rm fail}+800$ осталось 51 floor-запись, положительных сертификатов не возникло, а error enclosure перестал сокращаться.

## Зарегистрированные прогнозы до вывода



```
A:
  обычный Sturm-аргумент непосредственно к hλ не применим,
  потому что hλ — комбинация двух разных собственных функций.
  Прогноз: continuum sign сведётся к outer-lobe ratio + одному point gate.

B:
  corrected Poisson сам знак не докажет — только перенесёт его.
  Прогноз: останется signed quadrature-order theorem для h0/h4.
```

Оба прогноза подтвердились.

------

# 1. SOURCE LOCK

Имеем
$$
L_\lambda f
:=
-\frac{d}{dx}
\left((\lambda^2-x^2)f'(x)\right)
+
(2\pi\lambda x)^2f(x),
$$
и две вещественные чётные собственные функции
$$
L_\lambda h_{0,\lambda}
=
\Theta_{0,\lambda}h_{0,\lambda},
\qquad
L_\lambda h_{4,\lambda}
=
\Theta_{4,\lambda}h_{4,\lambda},
$$
с
$$
\Theta_{0,\lambda}<\Theta_{4,\lambda}.
$$
Канонический пакет с фазой `+`:
$$
\boxed{
h_\lambda
=
\frac{
I_{4,\lambda}h_{0,\lambda}
-
I_{0,\lambda}h_{4,\lambda}
}{
D_\lambda
}},
\qquad
D_\lambda
=
\sqrt{I_{0,\lambda}^2+I_{4,\lambda}^2},
$$
Эта формула и midpoint zero-extension зафиксированы source-lock’ом 011.

Сжатый Fourier-оператор даёт
$$
I_{0,\lambda}
=
\chi_0h_{0,\lambda}(0),
\qquad
I_{4,\lambda}
=
\chi_2h_{4,\lambda}(0),
$$
где
$$
1>\chi_0>\chi_2>0.
$$
Индексный lock здесь именно
$$
h_{0,\lambda}\leftrightarrow\chi_0,
\qquad
h_{4,\lambda}\leftrightarrow\chi_2.
$$
Это следует из убывания eigenvalues angle-оператора и положительных Fourier-фаз для even indices $0,4$. [![img](https://www.google.com/s2/favicons?domain=https://arxiv.org&sz=128)arXiv](https://arxiv.org/html/2602.04022v1)

Поэтому
$$
\boxed{
h_\lambda(0)
=
\frac{
(\chi_2-\chi_0)
h_{0,\lambda}(0)h_{4,\lambda}(0)
}{D_\lambda}
<0.
}
$$
Каждая order-zero spheroidal функция степени $n$ имеет ровно $n$ нулей в $(-1,1)$. Следовательно, $h_{4,\lambda}$ имеет ровно два положительных простых нуля в $(0,\lambda)$. [![img](https://www.google.com/s2/favicons?domain=https://dlmf.nist.gov&sz=128)DLMF](https://dlmf.nist.gov/30.4?utm_source=chatgpt.com)

------

# 2. ЛЕММА A

## Вердикт

$$
\boxed{
\texttt{REDUCED\_TO(HlambdaOuterLobeGate)}
}
$$

Точная оставшаяся подлемма состоит из **двух скалярных строгих неравенств**:
$$
\boxed{
\Theta_{4,\lambda}
>
\frac{17\pi^2}{4}\lambda^2
}
\tag{A-eig}
$$
и
$$
\boxed{
I_{0,\lambda}h_{4,\lambda}(1)
-
I_{4,\lambda}h_{0,\lambda}(1)
>0.
}
\tag{A-point}
$$
Из них пером полностью следует
$$
\boxed{
h_\lambda(x)<0,
\qquad
1\le x<\lambda.
}
$$
Midpoint-значение в $x=\lambda$ сохраняет этот знак, поэтому получаем требуемое $h_\lambda\le0$ на всём $[1,\lambda]$.

------

## 2.1 Первый нож: один нуль $h_4$ обязан лежать левее $1$

Обозначим
$$
p(x):=\lambda^2-x^2,
\qquad
q(x):=4\pi^2\lambda^2x^2,
\qquad
y(x):=h_{4,\lambda}(x).
$$
Уравнение имеет вид
$$
(p y')'+(\Theta_4-q)y=0.
$$
Предположим противное: $y$ не имеет нуля в $(0,1)$. Поскольку
$$
h_{4,\lambda}(0)>0,
$$
получаем
$$
y(x)>0
\qquad(0\le x\le1).
$$
Положим
$$
\delta
:=
\Theta_4-q(1)
=
\Theta_4-4\pi^2\lambda^2.
$$
Из `(A-eig)`:
$$
\delta>\frac{\pi^2}{4}\lambda^2.
$$
Чётность даёт $y'(0)=0$. Интегрируя уравнение:
$$
p(x)y'(x)
=
-\int_0^x
(\Theta_4-q(t))y(t)\,dt.
$$
На $[0,1]$:
$$
\Theta_4-q(t)\ge\delta,
$$
поэтому, если
$$
F(x):=\int_0^x y(t)\,dt,
$$
то
$$
p(x)y'(x)\le-\delta F(x).
$$
Так как
$$
p(x)\le\lambda^2,
$$
получаем
$$
F''(x)=y'(x)
\le
-\frac{\delta}{\lambda^2}F(x).
$$
Положим
$$
a^2:=\frac{\delta}{\lambda^2}.
$$
Тогда $a>\pi/2$. Сравним $F$ с $z(x)=\sin(ax)$. На интервале $0:
$$
\frac{d}{dx}\bigl(F'z-Fz'\bigr)
=
(F''+a^2F)z
\le0.
$$
При $x\downarrow0$ Wronskian стремится к нулю. В точке
$$
x_*=\frac{\pi}{2a}<1
$$
имеем $z(x_*)=1$, $z'(x_*)=0$, поэтому
$$
F'(x_*)=y(x_*)\le0.
$$
Это противоречит предположению $y>0$ на $[0,1]$.

Следовательно,
$$
\boxed{
h_{4,\lambda}
\text{ имеет хотя бы один положительный нуль в }(0,1).
}
\tag{A1}
$$

------

## 2.2 `(A-point)` помещает оба положительных нуля левее $1$

Из `(A-point)`:
$$
I_0h_4(1)>I_4h_0(1)>0.
$$
Следовательно,
$$
h_4(1)>0.
$$
Но также $h_4(0)>0$. Все нули просты. Поэтому число нулей $h_4$ в $(0,1)$ чётно.

По `(A1)` оно положительно. Всего положительных нулей ровно два. Значит оба находятся в $(0,1)$:
$$
\boxed{
0<z_1<z_2<1.
}
\tag{A2}
$$
Следовательно,
$$
h_{4,\lambda}(x)>0,
\qquad
1\le x<\lambda.
$$

------

## 2.3 Wronskian делает ratio строго возрастающим на внешней лопасти

Основная функция $h_{0,\lambda}$ строго положительна в $(-\lambda,\lambda)$. Определим
$$
r(x):=
\frac{h_{4,\lambda}(x)}
{h_{0,\lambda}(x)}.
$$
Пусть
$$
W(x)
:=
p(x)
\left(
h_0h_4'-h_4h_0'
\right).
$$
Вычитая два eigen-equations:
$$
W'(x)
=
(\Theta_0-\Theta_4)h_0(x)h_4(x).
$$
На $[1,\lambda)$ обе функции положительны, значит
$$
W'(x)<0.
$$
Регулярность spheroidal solution в $x=\lambda$ даёт
$$
\lim_{x\uparrow\lambda}W(x)=0.
$$
Поэтому
$$
W(x)
=
(\Theta_4-\Theta_0)
\int_x^\lambda
h_0(t)h_4(t)\,dt
>0.
$$
Следовательно,
$$
\boxed{
r'(x)
=
\frac{W(x)}
{p(x)h_0(x)^2}
>0,
\qquad
1\le x<\lambda.
}
\tag{A3}
$$
Положим
$$
c_\lambda:=\frac{I_4}{I_0}.
$$
Тогда
$$
h_\lambda(x)
=
\frac{I_0h_0(x)}{D_\lambda}
\bigl(c_\lambda-r(x)\bigr).
$$
`(A-point)` эквивалентно
$$
r(1)>c_\lambda.
$$
По `(A3)`:
$$
r(x)\ge r(1)>c_\lambda,
\qquad x\ge1.
$$
Значит
$$
\boxed{
h_\lambda(x)<0,
\qquad1\le x<\lambda.
}
$$
Это завершает paper-proof reduction A.

------

## 2.4 Как 025/026 потребляют два скаляра

В dimensionless coordinate
$$
t=\frac{x}{\lambda}
$$
пусть сырые same-mode функции равны $\phi_0,\phi_4$, а
$$
J_j:=\int_{-1}^1\phi_j(t)\,dt>0.
$$
Coordinate lock даёт
$$
h_j(x)
=
\frac{\phi_j(x/\lambda)}
{\sqrt\lambda\,N_j},
\qquad
I_j
=
\frac{\sqrt\lambda\,J_j}{N_j}.
$$
Определим нормированную разность
$$
\boxed{
\Psi_\lambda(t)
:=
\frac{\phi_4(t)}{J_4}
-
\frac{\phi_0(t)}{J_0}.
}
$$
Тогда
$$
(A\text{-point})
\iff
\boxed{
\Psi_\lambda(1/\lambda)>0.
}
$$
Если
$$
\phi_j=\phi_{j,K}+R_{j,K},
\qquad
\|R_{j,K}\|_\infty\le\varepsilon_{j,K},
$$
то достаточно доказать
$$
\boxed{
\Psi_{\lambda,K}(1/\lambda)
>
\frac{\varepsilon_{4,K}}{J_4}
+
\frac{\varepsilon_{0,K}}{J_0}.
}
\tag{A-tail}
$$
025 уже подтвердил условно-точные оценки
$$
\|R_{j,K}\|_\infty\le |a_{j,K}|,
$$
а также cone $1/2$, contraction $3/16$, $L^2$, derivative и Fourier tail budgets. Единственный не поставленный input — certified interval для spheroidal eigenvalue $\Lambda$, который сейчас строит 026.

Для `(A-eig)` 026 должен выдать:
$$
\boxed{
\Theta_{4,-}
=
\Lambda_{4,-}+G
>
\frac{17\pi^2}{4}\lambda^2.
}
\tag{A-eig-cert}
$$
Итак, A теперь не continuum-sign problem. Это:



```
one eigenvalue lower bound
+
one point determinant at x=1
+
the proved Sturm–Wronskian transport.
```

------

# 3. ЛЕММА B

## Вердикт

$$
\boxed{
\texttt{REDUCED\_TO(FiniteCoreThetaOrderWithTailBudget)}
}
$$

Ни corrected Poisson, ни обычный Sturm сами по себе B не доказывают.

Но B точно сводится к конечной системе **полиномиальных inequalities** на tooth-band’ах с полностью явным хвостовым бюджетом 025.

------

## 3.1 Poisson сначала только переводит B на primal side

Замороженный corrected-Poisson contract для zero-mass packet:
$$
E_\star(h_\lambda,u)
=
E_{\rm dual}(\widehat h_\lambda,u^{-1})
-
\frac12\sqrt u\,h_\lambda(0).
$$
Origin counterterm обязателен, поскольку $h_\lambda(0)\ne0$.

Положим $u=v^{-1}$. Тогда
$$
E_\star(h_\lambda,v^{-1})
=
E_{\rm dual}(\widehat h_\lambda,v)
-
\frac{h_\lambda(0)}{2\sqrt v}.
$$
Поскольку $h_\lambda(0)<0$, требуемое B:
$$
E_{\rm dual}(\widehat h_\lambda,v)
\le
-\frac{|h_\lambda(0)|}{2\sqrt v}
=
\frac{h_\lambda(0)}{2\sqrt v}
$$
эквивалентно ровно
$$
\boxed{
E_\star(h_\lambda,v^{-1})\le0,
\qquad1\le v\le\lambda.
}
\tag{B-primal}
$$
То есть Poisson не дал знак. Он только показал, какой **точный right-Riemann sampling statement** надо доказать.

------

## 3.2 Каноническая комбинация убирает все L²-нормировки

Из
$$
h_\lambda
=
\frac{I_4h_0-I_0h_4}{D}
$$
получаем:
$$
E_\star(h_\lambda,v^{-1})\le0
\iff
\frac{E_\star(h_4,v^{-1})}{I_4}
\ge
\frac{E_\star(h_0,v^{-1})}{I_0}.
\tag{B-ratio}
$$
Это уже точное содержание B: **normalised sampling error режима 4 не меньше sampling error режима 0**.

Теперь положим
$$
z:=\frac1{\lambda v}.
$$
При
$$
1\le v\le\lambda
$$
имеем
$$
\lambda^{-2}\le z\le\lambda^{-1}.
$$
Для отдельной моды:
$$
E_\star(h_j,v^{-1})
=
\frac1{\sqrt{\lambda v}\,N_j}
\sum_{n\ge1}^{\star}
\phi_j(nz).
$$
Поскольку
$$
I_j=\frac{\sqrt\lambda\,J_j}{N_j},
$$
то
$$
\boxed{
\frac{E_\star(h_j,v^{-1})}{I_j}
=
\frac1{\lambda\sqrt v\,J_j}
\sum_{n\ge1}^{\star}
\phi_j(nz).
}
$$
Все $N_j$ сократились.

С общей положительной константой `(B-ratio)` становится
$$
\boxed{
S_\lambda(z)
:=
\sum_{n\ge1}^{\star}
\Psi_\lambda(nz)
\ge0,
\qquad
\lambda^{-2}\le z\le\lambda^{-1},
}
\tag{B-sampling}
$$
где
$$
\Psi_\lambda(t)
=
\frac{\phi_4(t)}{J_4}
-
\frac{\phi_0(t)}{J_0}.
$$
Это уже не global Fourier continuation и не Fejér residual. Это компактная sampling inequality на $[0,1]$.

------

## 3.3 На каждой tooth-band это один полином

Предположим
$$
\frac1{r+1}<z<\frac1r.
$$
Тогда активны ровно $n=1,\ldots,r$, и endpoint weight отсутствует:
$$
S_\lambda(z)
=
\sum_{n=1}^{r}\Psi_\lambda(nz).
$$
Если
$$
z=\frac1r,
$$
последний аргумент равен $1$, поэтому midpoint convention даёт
$$
S_\lambda^\star(1/r)
=
\sum_{n=1}^{r-1}\Psi_\lambda(n/r)
+
\frac12\Psi_\lambda(1).
$$
Пусть finite Legendre cores равны $\phi_{j,K}$, и определим
$$
\Psi_{\lambda,K}(t)
=
\frac{\phi_{4,K}(t)}{J_4}
-
\frac{\phi_{0,K}(t)}{J_0}.
$$
Поскольку finite Legendre core — полином, функция
$$
\boxed{
P_{r,K}(z)
:=
\sum_{n=1}^{r}
\Psi_{\lambda,K}(nz)
}
$$
является обычным конечным полиномом по $z$.

------

## 3.4 Точный хвостовой бюджет

Пусть
$$
\|R_{j,K}\|_\infty
\le
\varepsilon_{j,K}.
$$
Определим
$$
\boxed{
\varepsilon_{\Psi,K}
:=
\frac{\varepsilon_{4,K}}{J_4}
+
\frac{\varepsilon_{0,K}}{J_0}.
}
$$
Тогда
$$
\|\Psi_\lambda-\Psi_{\lambda,K}\|_\infty
\le
\varepsilon_{\Psi,K}.
$$
Следовательно, на открытой tooth-band:
$$
\left|
S_\lambda(z)-P_{r,K}(z)
\right|
\le
r\,\varepsilon_{\Psi,K}.
$$
На tooth $z=1/r$:
$$
\left|
S_\lambda^\star(1/r)-P_{r,K}^\star
\right|
\le
\left(r-\frac12\right)
\varepsilon_{\Psi,K},
$$
где
$$
P_{r,K}^\star
=
\sum_{n=1}^{r-1}
\Psi_{\lambda,K}(n/r)
+
\frac12\Psi_{\lambda,K}(1).
$$
Поэтому B следует из следующей одной named lemma.

------

## `FiniteCoreThetaOrderWithTailBudget`

Для каждого admissible $\lambda$, для каждого $r$, чья tooth-band пересекает
$$
[\lambda^{-2},\lambda^{-1}],
$$
доказать:
$$
\boxed{
\inf_{
z\in
[\lambda^{-2},\lambda^{-1}]
\cap
[1/(r+1),1/r]
}
P_{r,K}(z)
\ge
r\,\varepsilon_{\Psi,K}
}
\tag{B-band}
$$
на открытой части полосы, и для каждого relevant tooth:
$$
\boxed{
P_{r,K}^\star
\ge
\left(r-\frac12\right)
\varepsilon_{\Psi,K}.
}
\tag{B-tooth}
$$
Тогда:
$$
S_\lambda(z)\ge0
$$
на всём требуемом интервале, откуда:
$$
E_\star(h_\lambda,v^{-1})\le0,
$$
и по corrected Poisson:
$$
\boxed{
E_{\rm dual}(\widehat h_\lambda)(v)
\le
-\frac{|h_\lambda(0)|}{2\sqrt v}.
}
$$
Это полный paper-proof reduction B.

------

# 4. Что именно стало меньше

51 floor-запись из 024 больше не является 51 отдельной загадкой.

Они стали конкретными участками конечных полиномов
$$
P_{r,K}(z)
$$
с одним общим certified-tail budget
$$
r\,\varepsilon_{\Psi,K}.
$$
024 уже показал, что дальнейшее увеличение `dps` не сокращает текущий Taylor/mode error; это failure представления, не свидетельство положительного интервала.

025 дал именно недостающий representation layer:
$$
\text{finite Legendre core}
+
\text{exact recessive tail}.
$$
После 026 появляется proof-grade $\varepsilon_{\Psi,K}$, а inequalities `(B-band)` и `(B-tooth)` можно закрывать:

- Sturm sequence для полинома;
- Bernstein-basis positivity;
- rational interval subdivision;
- exact sum-of-squares certificate.

Это уже строгие доказательства, не численная sign-grid.

------

# 5. STRONGEST ATTACK

## Против A

Главное возражение:

> `(A-point)` — это почти исходный знак, только в одной точке.

Верно, но continuum исчез. До reduction требовалось доказать знак на всём $[1,\lambda]$. Теперь требуется:

1. одна eigenvalue lower bound;
2. одно scalar determinant в $x=1$.

Дальнейший перенос на весь интервал — чистый Sturm–Wronskian theorem.

Второе возражение:

> Канонический пакет не является eigenfunction; к нему нельзя применять Sturm oscillation.

Именно поэтому Sturm применяется только к $h_4$ и к ratio $h_4/h_0$, а не к $h_\lambda$. Этот type mismatch устранён.

Оставшаяся проблема: для бесконечной cofinal family надо доказать `(A-point)` и `(A-eig)` равномерно либо дать parametric certificate family. Три отдельные клетки этого не заменяют.

------

## Против B

Самое сильное возражение:

> Вы просто переименовали исходный sign theorem в полиномиальные inequalities.

Не полностью.

Исходный B включал:

- глобальный Fourier transform;
- условно сходящийся dual sum;
- Fejér/Cesàro convention;
- origin counterterm;
- midpoint teeth;
- две independently normalized prolate modes;
- infinite Legendre tails.

После reduction остались:
$$
\boxed{
\text{конечные полиномы }P_{r,K}
+
\text{одна явная tail allowance}.
}
$$
Это реальное `REPRESENTATION_PROGRESS`.

Но это ещё не conceptual sign theorem. Если у полиномов не обнаружится uniform structural positivity, B останется certificate-family route. Нельзя объявлять её закрытой по отсутствию положительных grid-points.

------

## Против использования 025

025 подтвердил всю алгебру хвоста, но не построил сам exact mode: без certified $[\Lambda_-,\Lambda_+]$ нельзя выбрать $K_0$, сформировать continued fraction и получить $\varepsilon_{j,K}$. Это ровно честный stop-код 025.

Поэтому:



```
025 algebra:
  proved conditional

026 Lambda fork:
  load-bearing

A/B final certificates:
  after 026
```

------

# ROUTE MAP

| Узел                                 | Статус                                 |
| ------------------------------------ | -------------------------------------- |
| Source formula, phases, zero mass    | **PROVED / LOCKED**                    |
| Corrected Poisson identity           | **frozen dependency, not redone here** |
| A continuum transport                | **PAPER_PROVED**                       |
| `HlambdaOuterLobeGate`               | **OPEN: two scalars**                  |
| B primal sampling equivalence        | **PAPER_PROVED**                       |
| Legendre-tail reduction              | **PAPER_PROVED**                       |
| `FiniteCoreThetaOrderWithTailBudget` | **OPEN: polynomial certificates**      |
| Legendre recessive-tail algebra      | **PROVED CONDITIONAL**                 |
| Certified $\Lambda$-fork             | **ACTIVE 026**                         |



------

# FINAL PROPOSAL

Порядок A → B оставляем.

## После 026 первый exact target



```
HlambdaOuterLobeGate
```

Inputs:
$$
[\Lambda_{4,-},\Lambda_{4,+}],
\qquad
\phi_{0,K},\phi_{4,K},
\qquad
\varepsilon_{0,K},\varepsilon_{4,K}.
$$
Success:
$$
\Lambda_{4,-}+G
>
\frac{17\pi^2}{4}\lambda^2,
$$
Output:
$$
\boxed{h_\lambda\le0\text{ on }[1,\lambda].}
$$

## Затем B



```
FiniteCoreThetaOrderWithTailBudget
```

Не запускать ещё один sign probe. Строить exact polynomial certificates для `(B-band)` и `(B-tooth)`.

------

# CODEX DIRECTIVE



```
TARGET:
HlambdaOuterLobeGate

INPUTS:
- certified interval for project eigenvalue Theta4;
- exact finite Legendre cores phi0_K, phi4_K;
- certified sup-tail bounds eps0_K, eps4_K;
- positive source integrals J0,J4.

PROVE:
1. Theta4_lower > (17*pi^2/4)*lambda^2.
2. Psi_K(1/lambda) >
     eps4_K/J4_lower + eps0_K/J0_lower.
3. Instantiate the paper theorem:
     h_lambda(x) <= 0 for all x in [1,lambda].

FORBIDDEN:
- no grid sign;
- no direct Sturm theorem on h_lambda;
- no truncated eigenvector as exact mode;
- no mu := 1;
- no theorem weakening.

VALIDATION:
- exact/rational or outward-rounded inequalities;
- tail interval genuinely consumed;
- endpoint midpoint handled separately.

SUCCESS:
HLAMBDA_LAST_POSITIVE_ZERO_LT_ONE_PROVED

FAILURE:
HLAMBDA_EIGENVALUE_BARRIER_GAP
HLAMBDA_OUTER_POINT_DETERMINANT_GAP
```

После этого один следующий target — `FiniteCoreThetaOrderWithTailBudget`.

------

# META CLOSEOUT

**Что стало меньше?**

A:
$$
\text{sign on an interval}
\longrightarrow
\boxed{\text{two scalar inequalities}}.
$$
B:
$$
\text{global Poisson/dual sign}
\longrightarrow
\boxed{\text{finite polynomial positivity + explicit tail}}.
$$
**Что было убито?**

- прямое применение Sturm к канонической комбинации;
- идея, что corrected Poisson сам создаёт знак;
- дальнейшая decimal ladder;
- raw dual `tsum`;
- finite Legendre truncation без recessive tail.

**Текущие smallest named gaps:**
$$
\boxed{\texttt{HlambdaOuterLobeGate}}
$$
и затем
$$
\boxed{\texttt{FiniteCoreThetaOrderWithTailBudget}}.
$$
**Progress class:** `REPRESENTATION_PROGRESS`.

**Route score:** $5/5$.