# STATUS: CONDITIONAL — Ы, МАРШРУТ РАБОТАЕТ ПОСЛЕ ТРЁХ ТОЧНЫХ РЕМОНТОВ

```yaml
PRIMARY: TRY_GROUND_REALZERO_CURVATURE_VITALI_WITH_PRODUCTION_RATE_REPAIR
PRIMARY_COUNT: 1
DECISION: GO

ABSTRACT_CURVATURE_TO_NORMALITY:
  STATUS: PAPER_PASS
  SCOPE: ABSTRACT
  VERIFIER: PAPER

P59_SECOND_DERIVATIVE_FORMULA:
  STATUS: PAPER_PASS_NOT_LEAN_PROVED
  SCOPE: FINITE_CELL
  VERIFIER: PAPER

MOVING_NODE_VITALI_IDENTIFICATION:
  STATUS: PAPER_PASS
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER

TERMINAL_ZERO_ESCAPE:
  STATUS: LEAN_PROVED
  THEOREM: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  SCOPE: ABSTRACT
  VERIFIER: LEAN

PRODUCTION_SCHEDULE:
  EXACT: m_k = N_k = k + 2
  N_OVER_LOG_M_SQUARED: TENDS_TO_INFINITY
  NEW_SCHEDULE_REQUIRED: false

MINIMAL_CONSUMER_INTERFACE:
  CURVATURE:
    kappa_k: -F_k''(0) / (2 * F_k(0))
    required: eventually F_k(0) != 0 and sup_k kappa_k < infinity
  MOVING_LATTICE:
    required: A_k * sqrt(L_k) * sqrt(r_k) -> 0

ONE_RATE_SUFFICIENT_INTERFACE:
  A_k: norm(centeredXi(0) / rawFplus_k(0))
  r_k: selectedFerrersTrackedGroundResidualFloorRatio(P, beta, k)
  B_k: A_k * L_k^(5/2) * sqrt(r_k)
  sufficient_condition: B_k is eventually bounded
  necessary_condition: false

FULL_ROUTE_STATUS: OPEN_SOURCE_SUPPLIER
LEAN_EDIT_PERFORMED: false
JUDGE_KERNEL_RERUN: false
NUMERICAL_RUN_PERFORMED: false

K8A:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized entire finite-ground family has only real zeros and
    converges locally uniformly to centeredXi on the centered critical strip.
  ORIGINAL_REQUESTED_OBJECT: HumpMassBound / full exponential-moment normality
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - bounded normalized curvature plus moving-lattice convergence
    - one-rate sufficient condition B_k = O(1)
    - direct scalar curvature-functional resolvent estimate
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: real-zero curvature normality plus moving-node identification

NEXT_LOAD_BEARING_GAP:
  P59_NORMALIZED_CURVATURE_SOURCE_BOUND_ON_TRACKED_GROUND

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## Жёсткий ответ

**Да. Логическое ядро маршрута настоящее. Это не красивая байка.**

Он действительно заменяет старую тяжёлую задачу:

\[
\text{полный экспоненциально-взвешенный контроль на полосе}
\]

на существенно более узкую пару:

\[
\boxed{
\text{ограниченная кривизна в нуле}
+
\text{сходимость на сгущающейся решётке}.
}
\]

После этого **теорема Витали** даёт локально равномерную сходимость, а уже существующий **ZeroEscape** закрывает RH.

Но идти ровно по тексту файла нельзя. Там есть три ремонта:

1. кривизну надо нормировать с точным множителем \(1/2\);
2. новый кофинальный путь не нужен — production-путь уже сильнее;
3. сырой `sign ±1` и условие \(L^5\delta/\gamma=O(1)\) надо заменить точной complex/anchor-нормировкой проекта.

Сам замысел файла — основной **Curvature–Vitali route** — после этих правок я принимаю. fileciteturn653file0

---

# 1. Главный абстрактный мост действительно работает

Пусть:

\[
G_k(z)=\frac{F_k(z)}{F_k(0)},
\qquad
G_k(0)=1,
\]

и для каждого \(k\):

- \(G_k\) — целая функция;
- \(G_k(-z)=G_k(z)\);
- \(G_k\) вещественна на вещественной оси;
- все нули \(G_k\) вещественны;
- порядок \(G_k\) не превосходит \(1\).

Тогда **факторизация Адамара** — представление целой функции конечного порядка через её нули — даёт:

\[
G_k(z)
=
\prod_{\rho\in Z_k^+}
\left(1-\frac{z^2}{\rho^2}\right)^{m_k(\rho)}.
\]

Почему не остаётся лишний множитель \(e^{a_kz+b_k}\):

- чётность убивает \(e^{a_kz}\);
- условие \(G_k(0)=1\) убивает константу;
- порядок \(\le1\) запрещает множители вроде \(e^{az^2}\).

Теперь вводим точную **нормированную кривизну**:

\[
\boxed{
\kappa_k
:=
-\frac{G_k''(0)}2
=
-\frac{F_k''(0)}{2F_k(0)}.
}
\]

Тогда:

\[
\kappa_k
=
\sum_{\rho\in Z_k^+}
\frac{m_k(\rho)}{\rho^2}
\ge0.
\]

И для любого \(z\in\mathbb C\):

\[
\begin{aligned}
|G_k(z)|
&\le
\prod_{\rho\in Z_k^+}
\left(1+\frac{|z|^2}{\rho^2}\right)^{m_k(\rho)}
\\
&\le
\exp\left(
|z|^2
\sum_{\rho\in Z_k^+}\frac{m_k(\rho)}{\rho^2}
\right)
\\
&=
e^{\kappa_k|z|^2}.
\end{aligned}
\]

Следовательно:

\[
\boxed{
\sup_k\kappa_k<\infty
\quad\Longrightarrow\quad
\{G_k\}\text{ локально равномерно ограничено на }\mathbb C.
}
\]

Это полноценная **normal-family criterion** — достаточная оценка для нормальности семейства.

### Поправка множителя

В файле смешаны два обозначения:

\[
-\frac{F_k''(0)}{F_k(0)}
\]

и

\[
-\frac{F_k''(0)}{2F_k(0)}.
\]

Для суммы обратных квадратов нулей правильна именно вторая:

\[
\boxed{
\sum_{\rho>0}\frac{m(\rho)}{\rho^2}
=
-\frac{F''(0)}{2F(0)}.
}
\]

Первая величина просто вдвое больше. Для boundedness это не фатально, но в theorem statement множитель надо заморозить правильно.

### Почему гипотезы реально несущие

Без чётности возьми:

\[
G_n(z)=e^{nz}.
\]

Нулей нет, \(G_n(0)=1\), а величины \(-G_n''(0)/2\) ограничены сверху. Но семейство взрывается при \(\Re z>0\).

Без ограничения порядка возьми:

\[
G_n(z)=e^{nz^4}.
\]

Функции чётные, нулей нет, кривизна в нуле равна нулю, но семейство не локально ограничено.

Поэтому именно комбинация:

```text
even
+ real entire
+ real zeros
+ order <= 1
+ nonzero anchor
```

делает скалярную кривизну управляющей всем графиком. `[ABSTRACT][PAPER]`

---

# 2. Расчёт принудительных нулей правильный, но schedule менять не надо

У Proposition-59 transform есть общий sine-фактор. В точках:

\[
z_j=\frac{2\pi j}{L},
\qquad |j|>N,
\]

нет снимаемого полюса, поэтому:

\[
F_k(z_j)=0.
\]

Их вклад в положительную половину zero ledger:

\[
\kappa_k^{\mathrm{forced}}
\ge
\frac{L_k^2}{4\pi^2}
\sum_{j>N_k}\frac1{j^2}
\sim
\frac{L_k^2}{4\pi^2N_k}.
\]

Это хороший falsifier из файла.

Но отсюда следуют два разных режима:

\[
\kappa_k^{\mathrm{forced}}=O(1)
\quad\Longleftarrow\quad
N_k\gtrsim L_k^2;
\]

\[
\kappa_k^{\mathrm{forced}}\to0
\quad\Longleftarrow\quad
\frac{N_k}{L_k^2}\to\infty.
\]

Для нормальности требуется только первое. Второе — приятный усиленный вариант.

Главное: production schedule уже зафиксирован:

\[
m_k=N_k=k+2,
\qquad
L_k=\log(k+2).
\]

Поэтому:

\[
\frac{N_k}{L_k^2}
=
\frac{k+2}{\log^2(k+2)}
\longrightarrow\infty.
\]

То есть forced zeros здесь вообще не проблема. Новый путь:

\[
m_j=\lceil e^j\rceil,\qquad N_j=\lceil j^3\rceil
\]

не нужен и даже опасен: он переключит source-locked семейство без необходимости. Текущий Ferrers schedule уже удовлетворяет более сильному условию. fileciteturn663file0

**Вывод:** schedule-гейт зелёный. Используем только:

\[
\boxed{m_k=N_k=k+2.}
\]

---

# 3. **Ritz stability** правильна, но production-нормировка в файле неточная

**Ritz stability** — спектральная оценка, связывающая малый **Rayleigh defect** с близостью к ground state через **spectral gap**.

Для Hermitian \(H_k\), единичного trial \(q_k\), единичного ground state \(\xi_k\), ground eigenvalue \(\varepsilon_k\) и gap \(\gamma_k>0\):

\[
\delta_k
=
\langle q_k,H_kq_k\rangle-\varepsilon_k
\]

даёт:

\[
1-|\langle\xi_k,q_k\rangle|^2
\le
\frac{\delta_k}{\gamma_k}.
\]

После complex phase alignment:

\[
\inf_{|u|=1}\|\xi_k-uq_k\|^2
\le
\frac{2\delta_k}{\gamma_k}.
\]

Абстрактная формула файла верна.

Но production-объект уже имеет более точную схему. Положим:

\[
d_k=\langle\xi_k,q_k\rangle.
\]

Тогда используется не знак \(s_k\in\{\pm1\}\), а overlap-scaled вектор:

\[
d_k\xi_k.
\]

И:

\[
\boxed{
\|d_k\xi_k-q_k\|^2
=
1-|d_k|^2.
}
\]

В текущем Lean-слое это уже ограничено через точный **projective defect**:

\[
r_k
=
\frac{\|\operatorname{Residual}_k\|^2}{\beta_k^2}.
\]

А production-функции имеют вид:

\[
G_k=A_k\,T_k(q_k),
\]

\[
F_k=A_k\,T_k(d_k\xi_k),
\]

где:

\[
A_k
=
\frac{\operatorname{centeredXi}(0)}
     {\operatorname{rawFplus}_k(0)}.
\]

Репозиторий уже фиксирует именно этот tracked-ground scale и точную pointwise tracking inequality для того же real-zero ground object. fileciteturn670file0 fileciteturn674file0

Поэтому production-rate нельзя писать просто как:

\[
\frac{L_k\delta_k}{\gamma_k}\to0.
\]

Нужно учитывать anchor multiplier:

\[
\boxed{
|A_k|^2L_k\frac{\delta_k}{\gamma_k}\to0
}
\]

либо, в уже существующих объектах проекта:

\[
\boxed{
|A_k|\sqrt{L_k}\sqrt{r_k}\to0.
}
\]

Ещё одна правка: ориентировать ground-vector условием \(\xi_{k,0}>0\) пока нельзя. Ненулевость центральной координаты source theorem не поставляет. Используем \(d_k\), а затем нормируем целую функцию её eventual nonzero значением в нуле.

---

# 4. Формула второй производной тоже правильная

Для exact Proposition-59 transform:

\[
T_{L,N,\xi}(z)
=
L^{-1/2}
\sum_{|n|\le N}
\xi_n K_{L,n}(z)
\]

получается:

\[
\boxed{
T_{L,N,\xi}''(0)
=
-L^{5/2}
\left[
\frac{\xi_0}{12}
+
\frac1{2\pi^2}
\sum_{\substack{|n|\le N\\n\ne0}}
\frac{\xi_n}{n^2}
\right].
}
\]

Знак и обе константы сходятся с exact removable-kernel definition. Репозиторий уже доказывает:

- entire-ness transform;
- точную \(L^{-1/2}\)-нормировку;
- lattice sampling;
- центральное значение \(\sqrt L\,\xi_0\). fileciteturn661file0

Норма соответствующей coefficient-functional вычисляется точно:

\[
\left(\frac1{12}\right)^2
+
2\sum_{n=1}^{\infty}
\left(\frac1{2\pi^2n^2}\right)^2
=
\frac1{144}+\frac1{180}
=
\frac1{80}.
\]

Поэтому:

\[
\boxed{
|T_{L,N,\xi}''(0)-T_{L,N,q}''(0)|
\le
\frac{L^{5/2}}{\sqrt{80}}\|\xi-q\|_2.
}
\]

Для production overlap-scaled difference:

\[
\boxed{
|F_k''(0)-G_k''(0)|
\le
\frac{|A_k|L_k^{5/2}}{\sqrt{80}}\sqrt{r_k}.
}
\]

И вот тут появляется самый сильный результат всего аудита.

---

# 5. Один количественный budget действительно может закрыть и A, и B′

Определим:

\[
\boxed{
\mathcal B_k
:=
|A_k|L_k^{5/2}\sqrt{r_k}.
}
\]

Предположим всего лишь:

\[
\boxed{
\sup_{k\gg1}\mathcal B_k<\infty.
}
\]

Тогда на production lattice:

\[
|F_k(z_{k,j})-G_k(z_{k,j})|
\le
|A_k|\sqrt{L_k}\sqrt{r_k}
=
\frac{\mathcal B_k}{L_k^2}
\longrightarrow0.
\]

Это закрывает moving-node input A.

В частности, при \(j=0\):

\[
F_k(0)-G_k(0)\to0.
\]

А trial-family нормирована так, что:

\[
G_k(0)=\operatorname{centeredXi}(0).
\]

Следовательно:

\[
F_k(0)\to\operatorname{centeredXi}(0)\ne0.
\]

Значит после отбрасывания конечного префикса \(F_k(0)\neq0\).

Одновременно:

\[
|F_k''(0)-G_k''(0)|
\le
\frac{\mathcal B_k}{\sqrt{80}}
=
O(1).
\]

Trial-family локально равномерно сходится к `centeredXi` на текущем условном source port, поэтому по формуле Коши её вторые производные на нуле ограничены. Значит \(F_k''(0)\) тоже ограничены.

Из:

\[
F_k(0)\to\Xi(0)\ne0
\]

получаем:

\[
\boxed{
\sup_{k\gg1}
\left|
-\frac{F_k''(0)}{2F_k(0)}
\right|
<\infty.
}
\]

А real-zero/even product показывает, что эта величина на самом деле вещественна и неотрицательна.

Итого:

\[
\boxed{
\mathcal B_k=O(1)
}
\]

одновременно даёт:

```text
moving-lattice tracking error -> 0;
nonzero ground anchor;
bounded normalized curvature;
normality of the same real-zero ground family.
```

Это настоящий жирный supplier. Не декоративная упаковка.

В Rayleigh notation достаточная форма:

\[
\boxed{
|A_k|^2L_k^5\frac{\delta_k}{\gamma_k}
=
O(1).
}
\]

Без доказанной ограниченности \(A_k\) писать только \(L^5\delta/\gamma=O(1)\) нельзя.

---

# 6. **Vitali**-часть корректна

**Теорема Витали–Портера** говорит: локально ограниченная последовательность голоморфных функций, сходящаяся на множестве с внутренней точкой сгущения, сходится локально равномерно.

Берём:

\[
E=\{0\}\cup\{1/n:n\ge1\}.
\]

Для каждого \(x\in E\) выбираем ближайший production lattice node:

\[
z_{k,j_k(x)}
=
\frac{2\pi j_k(x)}{L_k},
\qquad
z_{k,j_k(x)}\to x.
\]

Поскольку:

\[
\frac{N_k}{L_k}\to\infty,
\]

эти узлы eventually лежат внутри finite carrier.

Мы уже получили:

\[
F_k(z_{k,j_k(x)})
-
G_k(z_{k,j_k(x)})
\to0.
\]

Локально равномерная trial-сходимость даёт:

\[
G_k(z_{k,j_k(x)})\to\Xi(x).
\]

А bounded curvature даёт local boundedness \(F_k\). По оценкам Коши это означает uniform local equicontinuity, поэтому:

\[
F_k(x)-F_k(z_{k,j_k(x)})\to0.
\]

Следовательно:

\[
F_k(x)\to\Xi(x)
\qquad(x\in E).
\]

Витали теперь выдаёт:

\[
F_k\longrightarrow\Xi
\]

локально равномерно на centered strip.

После этого уже существующий Lean-consumer принимает ровно:

```text
every F_k entire;
every F_k has only real zeros;
F_k -> centeredXi locally uniformly;
```

и выводит `Q3.RH`. fileciteturn666file0

Таким образом, верхняя цепь полностью законна:

\[
\boxed{
\text{real-zero ground}
+
\text{bounded curvature}
+
\text{moving-node rate}
\Rightarrow
\text{local uniform convergence}
\Rightarrow
RH.
}
\]

`[COFINAL_FAMILY][PAPER]` для нового Vitali-моста и `[ABSTRACT][LEAN]` для финального ZeroEscape.

---

# ROUTE MAP

| Узел | Вердикт | Tags |
|---|---|---|
| Exact P59 entire transform и lattice sampling | **PROVED** | `[FINITE_CELL][LEAN]` |
| Real-zero + even + order \(\le1\) + bounded curvature ⇒ local boundedness | **PASS** | `[ABSTRACT][PAPER]` |
| Формула \(F''(0)\) и константа \(1/\sqrt{80}\) | **PASS, не формализовано** | `[FINITE_CELL][PAPER]` |
| Production schedule \(m=N=k+2\) проходит forced-zero test | **PASS** | `[COFINAL_FAMILY][PAPER]` |
| Ritz/projective reduction | **PASS после scale/phase repair** | `[FINITE_CELL][LEAN/PAPER]` |
| Moving-node + normality ⇒ local uniform convergence | **PASS** | `[COFINAL_FAMILY][PAPER]` |
| Real-zero ground family | **CONDITIONAL на sector/complement floors** | `[FINITE_CELL][LEAN]` |
| \(\mathcal B_k=O(1)\) или direct curvature supplier | **OPEN** | `[COFINAL_FAMILY][CONDITIONAL]` |
| Local uniform real-zero family ⇒ RH | **PROVED** | `[ABSTRACT][LEAN]` |

---

# STRONGEST ATTACK

Главное возражение:

> Не переименовали ли мы старый ground-to-trial tracking gap в \(\mathcal B_k\)?

**Частично да, но не полностью.**

Общий fallback:

\[
\mathcal B_k
=
|A_k|L_k^{5/2}\sqrt{r_k}
\]

всё ещё требует источникового контроля residual/floor ratio. Это не возникает из воздуха.

Но новый consumer количественно намного слабее прежнего compact-decay target. Старый source-ordered kernel на высоте \(|\Im z|=\sigma\) несёт рост примерно:

\[
e^{\sigma L_k}.
\]

Новый joint budget несёт только:

\[
L_k^{5/2}.
\]

То есть мы заменили степенной рост по \(m\):

\[
e^{\sigma\log m}=m^\sigma
\]

на полином по \(\log m\).

Это реальное уменьшение стены, а не смена названия.

При этом фраза из файла:

> «текущий head/tail–Feshbach package закроет curvature»

пока не доказана. Более того, старый fixed/adaptive even-tail cutoff уже получил точное obstruction: cutoff лежит за пределами production carrier на выбранных Ferrers cells. Поэтому старый tail package нельзя просто вызвать повторно. fileciteturn662file6

Новый direct source attack должен быть функционально точным:

\[
\boxed{
\text{оценивать именно }
-\frac{F_k''(0)}{2F_k(0)},
\text{ а не весь вектор и не весь compact transform.}
}
\]

---

# Самый эффективный порядок теперь

## 1. Сначала закрыть абстрактный curvature bridge

Точный theorem shape:

```text
even entire
+ order <= 1
+ real on R
+ only real zeros
+ value at zero = 1
+ normalized curvature <= C
→ norm f(z) <= exp(C * norm(z)^2)
```

Это paper-pass. Lean-стоимость может оказаться выше ожидаемой из-за отсутствия готовой факторизации Адамара. Поэтому возможен более узкий P59-specific proof вместо общего entire-function framework.

## 2. Затем закрыть exact P59 second-jet identity

Публичное содержание:

```text
proposition59RawTransform_secondDerivative_zero
```

и:

```text
norm(secondDerivativeFunctional) <= L^(5/2) / sqrt(80)
```

Это самый дешёвый source-locked theorem. Никаких floor, RH или асимптотики здесь нет.

## 3. Потом атаковать самый слабый source consumer

Не сразу весь:

\[
\mathcal B_k=O(1).
\]

Первым идёт прямой скалярный target:

\[
\boxed{
\sup_k
\left|
-\frac{F_k''(0)}{2F_k(0)}
\right|
<\infty.
}
\]

Его надо пытаться получить через **dual/Schur functional** — оценку одной линейной функционали от ground vector, а не через полную норму ground-to-trial difference.

## 4. Только fallback — полный joint Ritz budget

Если direct scalar functional не поддаётся:

\[
\boxed{
|A_k|L_k^{5/2}\sqrt{r_k}=O(1).
}
\]

Он автоматически закрывает и lattice-rate, и curvature.

## 5. Затем один честный diagnostic run

Использовать только текущий schedule:

\[
m=N=k+2.
\]

Считать:

```text
L_k;
A_k;
r_k;
A_k * sqrt(L_k) * sqrt(r_k);
B_k = A_k * L_k^(5/2) * sqrt(r_k);
F_k(0);
F_k''(0);
kappa_k = -F_k''(0)/(2F_k(0));
forced kappa lower bound.
```

**Числа не доказывают кофинальный theorem.** Они должны решить только, куда вкладывать доказательство.

Заранее регистрирую:

```yaml
P_CURVATURE_SOURCE_1:
  probability: 0.65
  prediction: >-
    Exact normalized curvature remains bounded or stabilizes on the production
    schedule even if the old exponential moment ratio grows.

P_JOINT_PROJECTIVE_RATE_1:
  probability: 0.38
  prediction: >-
    The full sufficient budget A_k*L_k^(5/2)*sqrt(r_k) is bounded using the
    current residual/floor representation without a new source theorem.

P_DIRECT_FUNCTIONAL_BEATS_FULL_TRACKING_1:
  probability: 0.72
  prediction: >-
    A direct resolvent-weighted estimate of the 1/n^2 curvature functional is
    cheaper than proving the full projective B_k bound.
```

Текущий repository preflight честно сообщает, что ни direct ground normality, ни lattice-rate supplier пока на полке не найден. Это остаётся открытой аналитикой, а не Lean bookkeeping. fileciteturn668file0

# FINAL PROPOSAL

\[
\boxed{
\textbf{Да, идём этим маршрутом.}
}
\]

Но его правильная версия:

```text
finite tracked ground:
  entire + even + real zeros
             │
             ├── direct normalized-curvature bound
             │
             └── moving-lattice scalar rate
                        │
                        ▼
             Vitali local-uniform convergence
                        │
                        ▼
                  existing ZeroEscape
                        │
                        ▼
                       RH
```

**HumpMassBound больше не является обязательным объектом.**

Новый минимальный gap:

\[
\boxed{
\texttt{P59\_NORMALIZED\_CURVATURE\_SOURCE\_BOUND}
}
\]

а первый локальный удар — точная формула второй производной и норма \(1/\sqrt{80}\). Это уменьшает проблему, не выдаёт желаемое за доказанное и даёт дешёвый kill-test до месяцев работы.

Моя уверенность:

```text
абстрактный curvature → normality bridge: 0.98;
moving-node + Vitali logic:             0.95;
точная P59 second-derivative формула:   0.97;
маршрут как полезное ослабление B:      0.88;
текущий Feshbach package закроет source rate без новой математики: 0.35.
```

**Итог:** верх маршрута работает. Риск сосредоточен ровно в одном месте — source-контроле нормированной кривизны или достаточного joint Ritz budget. Это уже нормальная научная цель, а не туман.