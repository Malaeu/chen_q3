# STATUS: KILL_GOAL058_UNIFORM_LITERAL_COMPLEMENT_FLOOR

```yaml
OPERATIVE_CLASS: KILL_GOAL058_UNIFORM_LITERAL_COMPLEMENT_FLOOR
REQUESTED_RESULT: KILL_FLOOR
EVIDENCE_STATUS: PROVED_PAPER
REQUEST_ID: REQ-2026-09-25-INDEPENDENT-COMPLEMENT-FLOOR
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_LITERAL_CCM_COMPLEMENT_FLOOR
SOURCE_COMMIT: 6b7f2d981adcb894a3186a6c698e7e0f12b6ffa7
REQUEST_SHA256: 79207d2da49851bc31ff0899f1053aa0571955dac80f2395a11b7d255e6fbb1f
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
KILL_SCOPE: THEOREM_SHAPE
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILLED_OBJECT: one_fixed_positive_delta_for_the_literal_selected_trial_complement
HMODE_USED: previously_supplied_PAPER_full_window_rate_only
PROLATE_GAP_USED: false
ODD_SECTOR_FLOOR_USED: false
HRATIO_USED: false
SOURCE_RAYLEIGH_LIMIT_ASSUMED: false
FINITE_CELL_POSITIVITY_REFUTED: false
VARIABLE_POSITIVE_FLOOR_REFUTED: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
RUNTIME_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **KILL_FLOOR: одна постоянная \(\delta>0\) в сформулированном (FLOOR) невозможна.** С уже данным **PAPER hmode** получается кофинальное препятствие для **полной той же CCM-матрицы**, без предположений о знаке или пределе \(a_j\).

Это не вывод из отрицательного \(W02\). Построенные ниже **единичные комплексные тестовые векторы** удовлетворяют

\[
\boxed{
q_j^*y_j=0,\qquad
\operatorname{Re}y_j^*(K_j-a_jI)y_j\le U_j,
\qquad U_j\longrightarrow0.
}
\tag{K}
\]

Поэтому для любой предложенной постоянной \(\delta>0\), начиная с некоторого индекса,

\[
\boxed{
\operatorname{Re}y_j^*(K_j-a_jI-\delta I)y_j
\le U_j-\delta<-\delta/2<0.
}
\]

**Это отрицательная верхняя граница для самого проверяемого неравенства.** Положительный запас \(\delta_j\), зависящий от ячейки и стремящийся к нулю, этим не исключён. Простота ground state и весь Route B не опровергнуты.

**Мой предыдущий совет искать фиксированный `hfloorEv` как следующий независимый поставщик оказался слишком сильным.** Опровергается именно постоянный интерфейс, а не вся программа отслеживания ground-семьи.

:chatgpt-content-reference{index="11"}[Полный вердикт с доказательством и явными хвостовыми оценками — Markdown](sandbox:/mnt/data/goal058_independent_floor_20260925/VERDICT.md)

## 1. Что сохраняется буквально

Прочитаны все **5590 байт** запроса, **85 строк**, конечный LF. `PREPARED_NOT_SENT` не трактуется ни как свидетельство отправки, ни как математический допуск.

**[COFINAL_FAMILY | PAPER]** Фиксируем один \(P\). Всюду

\[
m=m_j=N_j=J_P+j+2,\qquad \lambda=\sqrt m,\qquad L=\log m,
\]

с тем же Ferrers cutoff \(5m\). Меняется только тестовый вектор внутри разрешённого \(q_j^\perp\), не источник и не расписание. Именно одна постоянная \(\delta\) требуется приложенным контрактом. :chatgpt-content-reference{index="0"}

В **логарифмической координате** \(t=\log u\):

\[
I_L=[-L/2,L/2],\qquad
\psi_{n,L}(t)=L^{-1/2}e^{2\pi in(t+L/2)/L}\mathbf1_{I_L}(t).
\]

Это исходниковый базис с мерой \(du/u=dt\). Фаза \((-1)^n\), все \(-m\le n\le m\), нулевая мода и комплексное сопряжение сохраняются. Норма коэффициентов — **евклидова сумма квадратов**, не sup-норма функционального типа.

`sourceCCMFiniteMatrix` — буквальная комплексизация `ccmWeilMatFinite`. `selectedFerrersFiniteCCMRow` — коэффициенты единично нормированной проекции именно `E_star(prolateCombination)`.  

Единственный используемый источниковый асимптотический вход — уже полученный **hmode**: ошибки \(C_n/m\) для центрированных физических мод на всём \([-\sqrt m,\sqrt m]\). Его пролатный спектральный зазор здесь не используется. Сохранённый в bus вердикт сообщает, что является сокращённой транскрипцией; расходуется явно записанное в нём **(HMODE)**, не выдуманный новый Lean-допуск. 

## 2. Полная матрица действительно является сжатием нужной формы

**[ABSTRACT | PAPER]** Для логарифмических функций положим

\[
C_{f,h}(x)=\int_{\mathbb R}\overline{f(t)}h(t+x)\,dt,
\qquad Q_{f,h}(x)=C_{f,h}(x)+C_{f,h}(-x).
\]

Рассмотрим **полную сесквилинейную форму Вейля**

\[
\begin{aligned}
\mathcal W(f,h)={}&
\int_0^\infty 2\cosh(x/2)Q_{f,h}(x)\,dx
-\frac{\gamma+\log(4\pi)}2Q_{f,h}(0)\\
&-\int_0^\infty
\frac{e^{x/2}Q_{f,h}(x)-Q_{f,h}(0)}{e^x-e^{-x}}\,dx\\
&-\sum_{\ell\ge2}\frac{\Lambda(\ell)}{\sqrt\ell}
Q_{f,h}(\log\ell).
\end{aligned}
\tag{W}
\]

Необходимая внешняя теорема — **явная формула Вейля**, а не её условие положительности и не RH. Нормировки сверены с CCM, §§2–4, в частности с формулами (2.9)–(2.10), (3.2), (3.10), (3.13)–(3.16). :chatgpt-content-reference{index="4"}

**Сопоставление с кодом здесь проверяется непосредственно.** Для \(0\le x\le L\):

\[
Q_{\psi_n,\psi_l}(x)=
\begin{cases}
2(1-x/L)\cos(2\pi nx/L),&n=l,\\[1mm]
\dfrac{\sin(2\pi lx/L)-\sin(2\pi nx/L)}{\pi(n-l)},&n\ne l.
\end{cases}
\]

Это ровно **`ccmQKernel`**, включая отдельную диагональную ветвь. Корреляция равна нулю при \(|x|>L\), поэтому prime-сумма становится **полной суммой \(2\le\ell\le m\)**.

Для архимедова хвоста:

\[
\int_L^\infty\frac{dx}{e^x-e^{-x}}
=-\frac12\log\tanh(L/2),\qquad
\tanh(L/2)=\frac{m-1}{m+1}.
\]

Это даёт именно логарифм в **`ccmWREntry`**. Первый член получается из точных интегралов

\[
\int\psi_{n,L}(t)e^{\pm t/2}\,dt
=
\frac{2\sinh(\pm L/4)}
{\sqrt L(\pm1/2+2\pi in/L)},
\]

и совпадает с **`ccmW02Entry`**. Следовательно,

\[
\boxed{\mathcal W(\psi_{n,L},\psi_{l,L})=K_m(n,l).}
\tag{C}
\]

**Ни диагональ, ни архимедова константа, ни prime powers не удалены.** Это бумажное доказательство совпадения форм; готовая Lean-реализация бесконечномерного перехода не заявляется. Определения всех трёх частей прочитаны на pin. 

## 3. Два точных нулевых направления полной формы

**[ABSTRACT | PAPER]** Обозначим

\[
\mathscr D_n(x)=D_n(2\sqrt\pi x),
\]

и возьмём **именно предельную комбинацию выбранного источника**:

\[
h_*(x)=3\mathscr D_0(x)-\mathscr D_4(x)
=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},
\]

\[
G(t)=e^{t/2}\sum_{r\ge1}h_*(re^t).
\tag{G}
\]

Прямое преобразование гауссиана даёт

\[
\mathcal F_+h_*=h_*,
\qquad h_*(0)=0,\qquad \int h_*=0,
\]

где физическое Fourier-ядро — \(e^{2\pi ixy}\). По **формуле Пуассона**

\[
G(-t)=G(t).
\]

Все производные \(G\) убывают быстрее любой экспоненты при \(|t|\to\infty\): справа это гауссова сумма, слева — точная симметрия. Кроме того, \(G\ne0\): при \(t\ge0\) каждое слагаемое в (G) строго отрицательно.

Для **логарифмического Fourier-преобразования**

\[
\widehat G(z)=\int_{\mathbb R}G(t)e^{-izt}\,dt,
\qquad s=\frac12-iz,
\]

сначала при \(\operatorname{Re}s>1\) имеем

\[
\begin{aligned}
\widehat G(z)
&=\zeta(s)\int_0^\infty h_*(x)x^{s-1}\,dx\\
&=2s(1-s)\pi^{-s/2}\Gamma(s/2)\zeta(s)\\
&=\boxed{-4\xi_\zeta(s)}.
\end{aligned}
\tag{M}
\]

Здесь \(\xi_\zeta(s)=\frac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\). Обе стороны целые, поэтому равенство продолжается всюду. Это вспомогательная стандартная \(\xi_\zeta\), **не перенормировка project `centeredXi`**.

Следовательно, \(\widehat G\) обращается в ноль во всех точках

\[
z_\rho=i(\rho-1/2)
\]

для нетривиальных нулей \(\zeta\), **где бы они ни находились**. Также

\[
\widehat{G''}(z)=-z^2\widehat G(z).
\]

В явной формуле для \(\mathcal W(G,f)\) каждый член содержит нулевой множитель. Для вещественных чётных \(G,G''\) сопряжение первого аргумента сохраняет это зануление. Поэтому

\[
\boxed{\mathcal W(G,f)=\mathcal W(G'',f)=0.}
\tag{R}
\]

Применимость явной формулы здесь обеспечена: свёртка гладкой сверхэкспоненциально убывающей функции с компактным оконным синтезом удовлетворяет её условиям. Смешанные prime-суммы абсолютно сходятся. **Положение нулей на критической линии не предполагается.** :chatgpt-content-reference{index="6"}

Получим фиксированные ортонормированные функции:

\[
g_0=\frac{G}{\|G\|_2},
\qquad
\kappa=\|g_0'\|_2^2,
\qquad
g_1=\frac{g_0''+\kappa g_0}{\|g_0''+\kappa g_0\|_2}.
\tag{O}
\]

Интегрирование по частям даёт \(g_0\perp g_1\). Знаменатель ненулевой: иначе \(g_0''+\kappa g_0=0\), а постоянная энергия этого ODE вместе с убыванием на бесконечности заставила бы \(g_0=0\).

**Обе функции принадлежат нуль-пространству формы (R).** Это ещё не нулевые векторы конечной матрицы — следующий переход обязателен.

## 4. Решающий стык: невязки конечных проекций действительно стремятся к нулю

**[COFINAL_FAMILY | PAPER]** Для \(g=g_0\) или \(g_1\) положим

\[
p_m=\Pi_m(g|_{I_L}),
\qquad b_m=\operatorname{coeff}_{\psi}(p_m).
\]

Докажем **нормовую**, а не только энергетическую малость:

\[
\boxed{\|K_m b_m\|_2\le\epsilon_g(m),\qquad \epsilon_g(m)\to0.}
\tag{N}
\]

### Fourier-проекция: производная и границы сохранены

Пусть

\[
B_g=\frac{\|g''\|_1+2\|g'\|_\infty}{4\pi^2}.
\]

Так как \(g(-L/2)=g(L/2)\), первый граничный член интегрирования по частям исчезает. Второй **остаётся в \(B_g\)**. Поэтому при \(n\ne0\)

\[
|c_n|\le B_gL^{3/2}/n^2.
\]

Для внутренней ошибки \(e_m=p_m-g|_{I_L}\), при \(m\ge3\):

\[
\begin{aligned}
\|e_m\|_2&\le B_g\sqrt{2/3}\,L^{3/2}m^{-3/2},\\
\|e_m'\|_2&\le2\pi B_g\sqrt{2L/m},\\
|e_m(-L/2)|+|e_m(L/2)|&\le4B_gL/m.
\end{aligned}
\tag{P}
\]

Производная — внутренняя. **Нулевое продолжение не объявляется глобально \(H^1\).**

### Полный \(W02-WR-\mathrm{Prime}\) на внутренней ошибке

Пусть \(f=\sum z_n\psi_{n,L}\), \(\|z\|_2=\|f\|_2=1\). Тогда

\[
\|f\|_\infty\le\sqrt{(2m+1)/L}\le\sqrt{3m/L}.
\]

Получаем следующие строгие оценки:

| Часть | Верхняя граница модуля смешанной формы |
|---|---|
| **\(W02\)** | \(2\sqrt m\,\|e_m\|_2\) |
| **Все Prime, \(2\le\ell\le m\)** | \(4\sqrt m\,L\,\|e_m\|_2\) |
| **\(WR\)** | \(13[2\|e_m'\|_2+2(|e_m(-L/2)|+|e_m(L/2)|)\sqrt{3m/L}]\) |

Для prime-строки достаточно

\[
|Q_{e_m,f}|\le2\|e_m\|_2,\qquad
0\le\Lambda(\ell)\le\log\ell,\qquad
\sum_{\ell\le m}\ell^{-1/2}\le2\sqrt m.
\]

**Гипотеза о распределении простых не нужна.**

В архимедовой строке используется точная ортогональность ошибки проекции:

\[
Q_{e_m,f}(0)=2\langle e_m,f\rangle=0.
\]

Перенос производной корреляции на \(e_m\) даёт

\[
|Q_{e_m,f}(x)|
\le x\left[
2\|e_m'\|_2+
2\bigl(|e_m(-L/2)|+|e_m(L/2)|\bigr)\|f\|_\infty
\right].
\]

Оба **endpoint jump-члена** включены. Затем

\[
\int_0^\infty \frac{x e^{x/2}}{e^x-e^{-x}}\,dx<13.
\]

Архимедова константа исчезла здесь **по доказанной ортогональности ошибки**, а не из-за удаления диагонали матрицы.

Итак, внутренний вклад ограничен явной величиной

\[
B_g\left[
\sqrt{2/3}\frac{(2+4L)L^{3/2}}m
+13(4\pi\sqrt2+8\sqrt3)\sqrt{L/m}
\right]\longrightarrow0.
\tag{I}
\]

### Внешний хвост, включая простые за \(m\)

Положим \(t_m=g\mathbf1_{I_L^c}\), \(b=L/2\),

\[
A_g(m)=\int_{I_L^c}e^{|t|/2}|g(t)|\,dt,
\qquad
T_g(m)=\|e^{|t|}g\mathbf1_{I_L^c}\|_2,
\]

\[
S_\Lambda=\sum_{\ell\ge2}\frac{\log\ell}{\ell^{3/2}}<\infty.
\]

Полный хвостовой вклад ограничен

\[
\begin{aligned}
\tau_g(m)={}&2m^{1/4}A_g(m)+2\sqrt m\,S_\Lambda T_g(m)\\
&+13\left[
2\|g'\mathbf1_{I_L^c}\|_2+
2\bigl(|g(-b)|+|g(b)|\bigr)\sqrt{3m/L}
\right].
\end{aligned}
\tag{T}
\]

Prime-оценка получается из

\[
|Q_{t_m,f}(x)|
\le2\sqrt m\,e^{-|x|}T_g(m),
\]

то есть из взвешенного Коши—Буняковского. **Сумма здесь бесконечная**, поскольку в разности с глобальным \(g\) появляется внешний хвост; он полностью оплачен, не отброшен.

Все члены (T) стремятся к нулю: при \(b=\frac12\log m\) хвосты (G) имеют вид \(m^A e^{-cm}\). Архимедова оценка сохраняет обе граничные массы.

Теперь

\[
\mathcal W(p_m,f)
=\mathcal W(p_m-g,f)
=\mathcal W(e_m-t_m,f)
\]

по (R). Берём supremum по единичным \(z\) и применяем точное (C). Получается (N), где \(\epsilon_g(m)\) — сумма правых частей (I), (T).

**Коммутативность проекции с формой не предполагалась.** Именно этот расчёт отличает доказательство от неправильного «глобальное ядро автоматически осталось ядром сжатия».

Gram-матрица двух проекций стремится к \(I_2\). Ортонормируем их в том же конечном carrier, получая \(u_m,v_m\). После фиксированного порога можно взять

\[
\varepsilon_m=6\bigl(\epsilon_{g_0}(m)+\epsilon_{g_1}(m)\bigr)\longrightarrow0
\]

так, что

\[
\boxed{
\sup_{\substack{w\in\operatorname{span}\{u_m,v_m\}\\\|w\|_2=1}}
\|K_mw\|_2\le\varepsilon_m.
}
\tag{S}
\]

## 5. Почему выбранный \(q_m\) имеет нужное перекрытие

**[COFINAL_FAMILY | PAPER]** Это единственное место использования **hmode**. Оценка \(Kq_m\) здесь не выводится и не требуется.

Берём буквальные центрированные моды с исходниковым нулевым продолжением:

\[
f_{0,m}=h_0/h_0(0),\qquad
f_{4,m}=3h_4/h_4(0).
\]

Пусть \(J_{0,m}=\int f_{0,m}\), \(J_{4,m}=\int f_{4,m}\). Из hmode и длины физического окна:

\[
J_{0,m}=1+O(m^{-1/2}),\qquad
J_{4,m}=3+O(m^{-1/2}).
\]

Направление `prolateCombination` **точно совпадает** с направлением

\[
H_m=J_{4,m}f_{0,m}-J_{0,m}f_{4,m}.
\tag{H}
\]

Общий ненулевой скаляр сокращается при конечной нормировке. Возможная фаза не меняет \(qq^*\), Rayleigh и абсолютное перекрытие. Это следует из буквальных определений интегралов \(I_0,I_4\) и знаменателя комбинации. 

Исходниковая карта:

\[
\mathcal E h(u)=\sqrt u\sum_{r\ge1}h(ru),
\]

затем окно и ортогональная проекция. 

Для каждой моды вклад ошибки от слагаемых внутри физического окна ограничен

\[
\sqrt u\,\frac{\lambda}{u}\frac{C_n}{m}
=\frac{C_n}{\sqrt m\sqrt u}.
\]

В правильной мере:

\[
\int_{1/\lambda}^{\lambda}
\frac{C_n^2}{m u}\frac{du}{u}
=
\frac{C_n^2}{m}(\lambda-\lambda^{-1})
=O(m^{-1/2}).
\]

Гауссовы слагаемые \(ru>\lambda\) дают экспоненциально малую добавку. Следовательно,

\[
\|\mathcal E f_{n,m}-\mathcal E\mathscr D_n\|_{L^2(\mathrm{window},du/u)}
=O(m^{-1/4}).
\]

Важный учёт масштаба: отдельные \(\mathcal E\mathscr D_0,\mathcal E\mathscr D_4\) **не объявляются глобально \(L^2\)**. Их нормы на текущем окне — \(O(m^{1/4})\). Поэтому ошибки \(J_n-d_n=O(m^{-1/2})\) в (H) дают ещё \(O(m^{-1/4})\).

Итого:

\[
\|\mathcal E H_m-\mathcal E(3\mathscr D_0-\mathscr D_4)\|_{L^2(\mathrm{window},du/u)}
\longrightarrow0.
\]

Проекция — сжатие в \(L^2\), а норма проекции \(G\) стремится к \(\|G\|_2>0\). После нормировки получаем

\[
\boxed{|\langle q_m,u_m\rangle|^2\longrightarrow1.}
\tag{A}
\]

**\(q_m\) не заменён \(u_m\).** Доказано только перекрытие, достаточное для следующего алгебраического шага.

## 6. Явный свидетель, не требующий предела \(a_j\)

**[ABSTRACT | PAPER]** Пусть \(K=K^*\), \(\|q\|=1\), \(a=q^*Kq\); \(u,v\) ортонормированы и

\[
|\langle q,u\rangle|^2\ge3/4,\qquad
\sup_{\substack{w\in\operatorname{span}\{u,v\}\\\|w\|=1}}\|Kw\|\le\varepsilon.
\]

Обозначим \(\alpha=\langle q,u\rangle\), \(\gamma=\langle q,v\rangle\).

### Случай 1: \(a\ge-6\varepsilon\)

Возьмём

\[
z=\frac{\alpha v-\gamma u}
{\sqrt{|\alpha|^2+|\gamma|^2}}.
\]

Тогда \(\|z\|=1\), \(q^*z=0\). **Лишнего сопряжения в числителе нет:** произведение линейно по второму аргументу.

\[
\boxed{z^*(K-aI)z\le\varepsilon-a\le7\varepsilon.}
\tag{B1}
\]

### Случай 2: \(a<-6\varepsilon\)

Возьмём \(w=u-\alpha q\). Тогда \(q^*w=0\), а точное раскрытие даёт

\[
\boxed{
w^*(K-aI)w
=
u^*Ku-2\operatorname{Re}(\overline\alpha\,q^*Ku)
+a(2|\alpha|^2-1).
}
\]

Следовательно,

\[
\boxed{w^*(K-aI)w\le3\varepsilon+a/2<0.}
\tag{B2}
\]

\(w\ne0\): иначе \(q\) и \(u\) коллинеарны и \(|a|\le\varepsilon\), противоречие. Поэтому \(w/\|w\|\) — единичный отрицательный свидетель.

Применяем эти два случая к настоящим \(a_j\), (S), (A). Определяем \(y_j\) соответствующей формулой и получаем (K) с

\[
\boxed{U_j=7\varepsilon_{m_j}\longrightarrow0.}
\]

Это удовлетворяет пункту 2 запроса: если неположительных quotients бесконечно много, они дают неограниченную подпоследовательность; иначе quotients eventually положительны и зажаты между \(0\) и \(U_j\), следовательно, стремятся к нулю. Во всех случаях постоянный **(FLOOR)** невозможен. :chatgpt-content-reference{index="9"}

**Отдельное доказательство \(a_j\to0\) не нужно.** Например,

\[
K_n=\operatorname{diag}(0,0,-n^4),\qquad
q_n=\left(\frac{n^2-1}{n^2+1},0,\frac{2in}{n^2+1}\right)
\]

имеет точную нулевую плоскость и \(q_n\to e_1\), но \(a_n\to-\infty\). Формула (B2) правильно обнаруживает отрицательное дополнение. Это контроль леммы, не замена CCM-источника.

## 7. Граница результата и контроль ошибок

**[ABSTRACT | PAPER]** Крайний тест **(E)** из запроса корректен. Но окончательное опровержение не требует знака его отдельной левой части.

В частности, отрицательный \(W02\) не был принят за полный отрицательный знак. На краю \(N=m\) сама архимедова часть имеет

\[
-WR(L;m,m)=\log(2\pi m/L)+O(1),
\]

что видно после выделения \(\int_0^1(1-\cos(2\pi mx/L))\,dx/x\). Это ничего не решает о полном prime-вкладе.

Проведены **35 точных алгебраических проверок**: сопряжения, проекции, оба случая (B1)/(B2), Mellin-полином и Fourier-инвариантность \(h_*\). Умышленно неправильная ортогонализация без сопряжения и подмена нормовой малости нулевой энергией отвергнуты. **CCM-спектры и численные сетки не вычислялись.** Аналитические пределы доказаны выше, не этими тестами.

| Предсказание | Судьба |
|---|---|
| **P1:** крайняя формула (E) точна | Подтверждено |
| **P2:** двухкоординатный тест убирает явную невязку | Подтверждено; полного знака сам не решил |
| **P3:** архимедова диагональ содержит положительный логарифмический вклад | Подтверждено бумажным разложением |
| **P4:** nullspace-атака обязательно требует отдельного контроля \(a_j\) | **Опровергнуто как требование** леммой (B1)/(B2) |
| **P5:** два приближённо нулевых направления дают \(7\varepsilon\) без предела \(a_j\) | Доказано |
| **P6:** полный перенос на конечную матрицу оплачивается | Доказано оценками (I), (T) |

Регистрации до тестов сохранены; P4 не переписано задним числом.

**Самая сильная атака на доказательство:** глобальное нуль-пространство не обязано переживать конечную проекцию. Именно поэтому несущий результат — **нормовая оценка (N)** с двумя границами и всеми prime-вкладами. Без §4 этот KILL был бы необоснован.

**Не установлены:** знак дополнения в каждой ячейке, положительность всего \(K_j\), существование подходящего \(\delta_j>0\), малость \(\|R_j\|/\delta_j\), полный G3. Prolate-gap, odd-tail supplier и условный Gram/Schur receiver не использованы.

## 8. Зависимости и следующий точный стык

```yaml
DOWNSTREAM_CONSUMER: selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors
ACTUAL_CONSUMER_REQUIREMENT: same_ground_family_with_real_zeros_and_locally_uniform_tracking
ORIGINAL_REQUESTED_OBJECT: fixed_positive_hfloorEv
ORIGINAL_OBJECT_IS: NOT_NECESSARY
QUALIFICATION: required_by_the_current_constant_floor_wrapper_not_by_the_terminal_family_statement
KNOWN_WEAKER_INTERFACES:
  - positive_cellwise_delta_j_for_the_literal_complement
  - same_tail_cellwise_extraction_with_fully_paid_delta_j_dependent_tracking
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE: explicit_y_j_and_U_j_in_sections_4_to_6
ROUTE_FAMILY_KILLED: false
REMAINING_RESEARCH_DEBT: variable_scale_source_floor_and_exact_consumer_fit
REOPEN_TRIGGER: independent_cellwise_floor_at_the_correct_scale_or_a_demonstrated_error_in_this_counterproof
NOVELTY_AXIS: Mellin_vanishing_plus_full_compression_residual_plus_Rayleigh_safe_two_plane_witness
```

**Что стало меньше:** исключён поиск невозможной одной положительной константы.

**Возможная достаточная замена** — положительные cellwise floors \(\delta_j\) с теми же объектами и полностью оплаченным tracking-бюджетом. Но они **не подставляются молча** в существующий constant-\(\beta\) wrapper: необходим отдельный проверенный переход. Ни положительность \(\delta_j\), ни нужная скорость этим вердиктом не поставлены.

Независимая внешняя приёмка нового PAPER-доказательства не заявлена. **Runtime, Lean, GitHub и route-state не менялись.**

## CODEX DIRECTIVE — `TRY_GOAL058_NULLPLANE_OBSTRUCTION_SOURCE_AUDIT`

**Один следующий бумажный target:** независимо воспроизвести §4 — нормовую оценку **(N)** для двух явных проекций **(O)** в буквальном carrier \(-m,\ldots,m\), затем проверить её подстановку в §6. Это наиболее уязвимый источниковый стык контрпримера, не очередной generic floor-wrapper.

Сохранить `SOURCE_COMMIT`, \(N=m\), фазу \((-1)^n\), diagonal `Q_L`, все prime powers, обе границы окна и тот же \(P\). **hmode использовать только для перекрытия (A). Не предполагать \(a_j\to0\), положительность \(K_j\), RH или коммутативность \(\Pi_m\) с формой.**

**Успех:** mixed-form bound (I)+(T) подтверждён; (B1)/(B2) дают \(U_j\to0\); фиксированный (FLOOR) регистрируется только как опровергнутая **theorem-shape**. **Остановка:** первый конкретный дефект form-identity, области явной формулы, Fourier boundary, хвостовой нормы или источниковой нормировки — с точной формулой.

**До этой проверки не продолжать поиск постоянного `hfloorEv`.** Возможный интерфейс с \(\delta_j\) не вводить автоматически: его положительность, кванторы и связь с тем же потребителем — отдельная доказательная задача. **Lean/runtime не запускать; RH-claim не делать.**