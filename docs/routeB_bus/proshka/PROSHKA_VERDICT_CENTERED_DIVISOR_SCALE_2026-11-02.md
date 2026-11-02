# STATUS: KILL_UNNORMALIZED_CENTERED_DIVISOR_REMAINDER

```yaml
OPERATIVE_CLASS: KILL_UNNORMALIZED_CENTERED_DIVISOR_REMAINDER
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_CENTERED_MULTIPLIER_SCALE_CHECK
TASK_MODE: MATHEMATICAL_REQUEST_NOT_FORMAL_TXT_BUS_ADJUDICATION
SOURCE_BRANCH_PIN: 0dbf384877d6d20af0bdb4369f43f93422b79547
SOURCE_PREFLIGHT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_DIVISOR_GRAM_PULLBACK_PREFLIGHT_2026-11-02.md
SOURCE_PREFLIGHT_BLOB: b780faf8aa71d25d4101009acd0fd5a7688e81e6
SOURCE_QUIET_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_QUIET_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_FLOOR_COMMIT: e724ae65ed39a8ba8b8f07c928d790ea9820342a
SOURCE_FLOOR_BLOB: 26eaa3ebe5f8fea7fadbdc6d1994654c4710b8c7
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
CARRIER: LITERAL_REAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
KILL_SCOPE: THEOREM_SHAPE
KILL_TARGET: q_m_MINUS_FIXED_POSITIVE_MULTIPLE_OF_UNNORMALIZED_CENTERED_DIVISOR_GRAM_HAS_CONSTANT_LOWER_FLOOR
KILL_EVIDENCE_KIND: COFINAL_NEGATIVE_UPPER_ENVELOPE_BY_RH_CASE_SPLIT
KILL_EVIDENCE_REFERENCE: THIS_FILE_SECTIONS_4_THROUGH_8
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_UNNORMALIZED_LIFT_ONLY
FINAL_RESULT_ASSUMES_RH: false
CONDITIONAL_INTERMEDIATE_BRANCH: RH
RH_BRANCH_IMPORTS: [Gonek_1984_Corollary_2, Montgomery_1973_Corollary_1_equation_6]
ZERO_SIDE_USED_FOR_POSITIVE_TARGET: false
ZERO_SIDE_USED_IN_OBSTRUCTION_RH_BRANCH: true
PROOF_IS_PRIME_SIDE_ONLY: false
SIMPLE_ZEROS_OR_PAIR_CORRELATION_CONJECTURE_ASSUMED: false
NORMALIZED_WEIGHT_SUM: EXACTLY_ONE
NORMALIZED_REMAINDER_LOWER_BOUND: NOT_PROVED
ORIGINAL_COMPLEMENT_FLOOR: OPEN
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
EXACT_LOCAL_CONTROL_GROUPS: 7
FLOATING_MULTIPLIER_SAMPLES: 16
FLOATING_FIXED_T_EXPANSION_SAMPLES: 9
NEW_CCM_EIGENPROBLEMS: 0
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
```

## 0. Результат

Получено PAPER-доказательство препятствия для ненормированного центрированного lift, а не только эвристика среднего значения. На точном расписании тихого пространства, для каждого фиксированного a>0,

\[
\boxed{\inf_{f\in J_m^\perp,\ \|f\|_2=1}
       \{q_m[f]-a\widetilde G_m[f]\}\longrightarrow-\infty.}
\tag{0.1}
\]

Итог не предполагает RH. Доказательство разделяет два случая. В случае RH на настоящих ядрах дополнения доказываются средние оценки \(\overline{\widetilde G_m}\ge cL^2\) и \(\overline{|q_m|}\le CL\). В случае not-RH унаследованные constant-floor и quiet-residual поставщики уже заставляют минимум q_m на дополнении уходить к минус бесконечности; вычитание неотрицательной формы этого не исправляет. Это запрет одного способа доказать исходный пол, не запрет исходного пола и не вывод RH.

Для скалярного перемасштабирования всего lift доказана необходимая цена: если \(a_m\ge0\) и \(q_m-a_m\widetilde G_m\ge-K\) на J_m-perp вдоль неограниченной семьи, то \(a_m=O(1/L)\) на этой семье. Поэтому нормировка общим весом порядка L обязательна в данном классе. Достаточность нормировки не доказана.

## 1. Источники и неизменённые определения

S1 — PREFLIGHT из header, §§1,4,7. Именно там определены
\[
q_m[f]=H_+[f]-P_m^{12}[f]+I_L[f],\quad
I_L[f]=\int_0^L e^{s/2}Q_f(s)\,ds,
\]
\[
\widetilde Z_Nf=\sum_{n\le N}n^{-1/2}f(\cdot+\log n)
 -\int_0^N u^{-1/2}f(\cdot+\log u)\,du,
\quad
\widetilde G_m[f]=\sum_{d=2}^m\frac{\Lambda(d)}d
       \|\widetilde Z_{\lfloor m/d\rfloor}f\|_2^2.
\tag{1.1}
\]
Выходные нормы считаются на всей прямой. Нижний конец континуума 0, не 1; сдвинутые хвосты не обрезаются. Вход сохраняет исходное окно, чётность, физическую L2-норму и N=m. Все простые степени присутствуют.

S2 — SHRINKING_KAPPA_INTERPOLATION_RESIDUAL на 2176dab, (0.1)–(0.5):
\[
L=\log m,\quad \Omega=2\pi m/L,\quad
T_m=\left(1+c_0\frac{1+\log L}{L}\right)\Omega,
\quad 0<c_0<1\text{ fixed},
\]
J_m задаётся actual complex-zero value-условиями ниже T_m, без добавления derivative-условий в кратных нулях. Для ортогональной проекции \(\Pi_m\) на J_m унаследовано \(\|A_m\Pi_m\|=\delta_m=o(m^{-B})\) при каждом фиксированном B. Используется только это конкретное расписание, не равномерность до kappa=1.

S3 — NOESCAPE_CONSTANT_FLOOR_REDUCTION на e724ae6: not-RH влечёт \(\lambda_{\min}(A_m)\to-\infty\); один постоянный полный нижний пол на неограниченной семье влечёт RH. S2/S3 используются как ранее принятые PAPER-поставщики, не как независимо проверенные заново результаты этой сессии.

Точный source-return из S1:
\[
q_m[f]=\mathfrak k[f]+(c_*-4)\|f\|^2+P_m^{\ge3}[f],
\quad |P_m^{\ge3}[f]|\le C_3\|f\|^2,
\quad C_3=(1+\sqrt2)(8+5\log2)<28.
\tag{1.2}
\]
Он верен также для используемых ниже компактных cosine-функций до проекции. Положим \(B_0=|c_*-4|+C_3\).

Внешние первичные источники:

P1. E.C. Titchmarsh, revised D.R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed., §4.11. Для явной безопасной константы используется J. Arias de Reyna, arXiv:2406.16667v1, Theorem 6: при sigma>=0, 0<t<=x ошибка центрированной суммы не превосходит (29/14)x^(-sigma), в частности 3x^(-sigma). Его формулировка и доказательство прочитаны. Это аналитическая теорема, не гипотеза о нулях.

P2. S.M. Gonek, *Mean values of the Riemann zeta-function and its derivatives*, Invent. Math. 75 (1984), 123–141, Corollary 2, equation (7), p.124. Используется ровно опубликованная RH-условная формула, включая её uniform-in-alpha error. Первичный текст прочитан; та же формула сверена визуально в Introduction arXiv:2512.03297v1. Новые теоремы последней статьи не импортируются.

P3. H.L. Montgomery, *The pair correlation of zeros of the zeta function*, Proc. Symp. Pure Math. 24 (1973), 181–193, Corollary 1, equation (6), p.182. Формула прочитана визуально. Нужен доказанный результат для фиксированного параметра <1, НЕ pair-correlation conjecture.

Техническая граница чтения: screenshot первичного PDF Гонека и книжного PDF Титчмарша вернул cache miss; их извлечённый текст доступен. Формулу Гонека дополнительно визуально сверено по указанной научной статье, а для Титчмарша использована читаемая явная версия P1. Это не независимый аудит всех доказательств P1–P3.

## 2. Правильный символ и область формулы Титчмарша

**[FINITE_CELL | PAPER; LA + analytic input P1.]** При \(s=1/2-it\) обозначим
\[
b_N(t)=\sum_{n=1}^N n^{-1/2+it}
             -\frac{N^{1/2+it}}{1/2+it}.
\]
Тогда точно
\[
\widetilde G_m[f]=\frac1{2\pi}\int_{\mathbb R}
 g_m(t)|\widehat f(t)|^2dt,\qquad
 g_m(t)=\sum_{d=2}^m\frac{\Lambda(d)}d
                   |b_{\lfloor m/d\rfloor}(t)|^2\ge0.
\tag{2.1}
\]
Для фиксированного t Euler–Maclaurin даёт
\[
b_N(t)=\zeta(s)+\tfrac12N^{-s}-\tfrac{s}{12}N^{-s-1}
                  +O_t(N^{-5/2}).
\tag{2.2}
\]
Последняя цена намеренно ослаблена; достаточно +1/2 N^(-s)+O_t(N^(-3/2)). Знак половинного члена в запросе правилен. При растущем t нельзя использовать fixed-t remainder. Для всей полосы \(|t|\le N\) P1 и сопряжение/непрерывность дают
\[
\boxed{|b_N(t)-\zeta(1/2-it)|\le3N^{-1/2}.}
\tag{2.3}
\]
Таким образом, замена b_N на zeta законна только на длинных суммах. Короткие суммы N<|t| остаются отдельным неотрицательным сектором.

### Полная масса весов

**[COFINAL_FAMILY | PAPER; E + ordinary-integer arithmetic.]**
\[
W(x)=\sum_{2\le d\le x}\frac{\Lambda(d)}d=\log x+O(1).
\tag{2.4}
\]
Это не требует RH или PNT. Для целого n точное divisor identity даёт
\[
\log(n!)=\sum_{d\le n}\Lambda(d)\lfloor n/d\rfloor
=nW(n)-\sum_{d\le n}\Lambda(d)\{n/d\}.
\]
Последняя сумма между 0 и \(\psi(n)\le4(\log2)n\) (элементарный Chebyshev-поставщик S1). Stirling или интегральная оценка log(n!) завершает (2.4).

Пусть \(M=\lceil2+|t|\rceil\), \(D=\lfloor m/M\rfloor\ge2\). Тогда N_d>=M и
\[
 g_m^{long}(t):=\sum_{2\le d\le D}\frac{\Lambda(d)}d|b_{N_d}(t)|^2
 =W(D)|\zeta(1/2-it)|^2+
 O\!\left(|\zeta(1/2-it)|\sqrt{D/m}+D/m\right).
\tag{2.5}
\]
Константа абсолютная. Действительно, N_d>=m/(2d),
\(\sum_{d\le D}\Lambda(d)/\sqrt d\le8\log2\sqrt D\),
\(\sum_{d\le D}\Lambda(d)\le4\log2 D\). Применить
\(\big||z+r|^2-|z|^2\big|\le2|z||r|+|r|^2\) и (2.3).

Остаток \(g_m-g_m^{long}\ge0\) не удаляется. Поэтому запись из запроса описывает main coefficient длинного сектора, но не доказанную эквивалентность полного g_m на всех частотах. В частности, при фиксированном t полный символ равен
\[
g_m(t)=L|\zeta(1/2-it)|^2+O_t(1),
\tag{2.6}
\]
поскольку короткий сектор тогда содержит лишь ограниченные N, а суммарный вес этих d равен O_t(1). Квадрат L здесь появляется лишь после moving-height averaging, а не при фиксированной частоте.

## 3. Явная нижняя оценка длинного сектора

**[FINITE_CELL | PAPER; E + LA + P1, без RH.]** Для \(Y=m^{1/4}\) возьмём
\[
D_m=\lfloor m/(4Y+2)\rfloor.
\]
При d<=D_m имеем N_d>=4Y, а для |t|<=2Y формула (2.3) применима. Из
\(|z+r|^2\ge\tfrac12|z|^2-|r|^2\) следует
\[
\boxed{g_m(t)\ge\tfrac12W(D_m)|\zeta(1/2-it)|^2-C_1/Y,
\qquad |t|\le2Y.}
\tag{3.1}
\]
Например, \(\sum_{d\le D_m}(\Lambda(d)/d)N_d^{-1}\le8\log2 D_m/m\), так что можно взять фиксированное C_1 из 9-кратного этого бюджета. По (2.4), \(W(D_m)=\tfrac34L+O(1)\). Все короткие N помогают этой НИЖНЕЙ оценке и потому могут быть отброшены здесь, но не в равенстве (2.5).

Также на всём L2
\[
\boxed{\|\widetilde G_m\|_{op}\le32m.}
\tag{3.2}
\]
В самом деле, \(\|Z_N\|\le2\sqrt N\), \(\|\mathcal C_N\|\le2\sqrt N\), следовательно \(\|\widetilde Z_N\|^2\le16N\). Далее
\(\sum\Lambda(d)/d^2\le\sum\log d/d^2<2\).
Это лишь бюджет проекционного возврата, не целевая bound на q_m.

## 4. Настоящие ядра дополнения и uniform projection budget

**[COFINAL_FAMILY | PAPER, conditional branch RH begins here.]** Временно предполагаем RH. Пусть \(\Gamma_Y\) — мультимножество ординат \(1<\gamma\le Y\) нулей, с кратностями, и \(n_Y=|\Gamma_Y|\asymp Y\log Y\). Для каждого из них
\[
v_{\gamma,L}(x)=\cos(\gamma x)\mathbf1_{[-L/2,L/2]}(x),
\quad u_{\gamma,L}=v_{\gamma,L}/\|v_{\gamma,L}\|,
\quad f_{\gamma,m}=P_mv_{\gamma,L}/\|P_mv_{\gamma,L}\|.
\tag{4.1}
\]
Здесь P_m — буквальная проекция на N=m, не увеличение носителя. Так как Y<T_m при больших m,
\(\langle P_mv_{\gamma,L},j\rangle=\widehat j(\gamma)=0\) для j in J_m. Поэтому каждый \(f_{\gamma,m}\in J_m^\perp\). Случай кратного нуля лишь повторяет член ансамбля; derivative-условий нет. Никаких eigenvectors или спектральных щелей не требуется.

\[
\|v_{\gamma,L}\|^2=L/2+\sin(\gamma L)/(2\gamma)\asymp L.
\]
Для n>m точный коэффициент cosine-проекции равен
\[
a_n=2\sqrt{2/L}\,
 \frac{\gamma(-1)^n\sin(\gamma L/2)}{\gamma^2-(2\pi n/L)^2}.
\]
При \(\Omega\ge\sqrt2Y\), равномерно по gamma<=Y,
\[
\|v-P_mv\|^2\le\frac{2\gamma^2L^3}{3\pi^4m^3},
\quad \|(v-P_mv)'_{int}\|^2\le\frac{8\gamma^2L}{\pi^2m},
\quad |(v-P_mv)(L/2)|\le\frac{2\gamma L}{\pi^2m}.
\tag{4.2}
\]
Следовательно
\[
\|f_{\gamma,m}-u_{\gamma,L}\|\le C\gamma Lm^{-3/2},
\quad
|\widetilde G_m[f_{\gamma,m}]-\widetilde G_m[u_{\gamma,L}]|
\le C\gamma Lm^{-1/2}=O(m^{-1/4}L)=o(1).
\tag{4.3}
\]
Во второй оценке используется полный операторный budget (3.2), включая все выходные хвосты. Это uniform return для растущих gamma, не fixed-profile o(1).

## 5. Средний centered Gram на дополнении имеет нижний масштаб L^2

Для \(1\le v\le2\), \(t=\gamma+v/L\),
\[
\widehat v_{\gamma,L}(t)
=L\frac{\sin(v/2)}v+
  \frac{\sin((2\gamma+v/L)L/2)}{2\gamma+v/L}.
\]
Первый член >=L/pi, второй по модулю <=1/2. При больших L получаем
\[
\frac{|\widehat u_{\gamma,L}(\gamma+v/L)|^2}{2\pi}
\ge\frac{L}{8\pi^3}.
\tag{5.1}
\]
Использование (3.1) только на этом интервале и неотрицательности g_m вне него даёт
\[
\widetilde G_m[u_{\gamma,L}]
\ge\frac{W(D_m)}{16\pi^3}
       \int_1^2|\zeta(1/2+i(\gamma+v/L))|^2dv-C_1/Y.
\tag{5.2}
\]

**Точный импорт P2, Corollary 2:** при RH, \(\ell_Y=\log(Y/(2\pi))/(2\pi)\),
\[
\sum_{1<\gamma\le Y}
 |\zeta(1/2+i(\gamma+\alpha/\ell_Y))|^2
=\left[1-\left(\frac{\sin\pi\alpha}{\pi\alpha}\right)^2\right]
\frac{Y}{2\pi}\log^2Y+O(Y\log Y),
\tag{5.3}
\]
равномерно в допустимой alpha; наш диапазон — фиксированный компакт внутри него.

Берём \(\alpha=v\ell_Y/L\). Тогда \(\pi\alpha\to v/8\), равномерно для 1<=v<=2, а квадратная скобка строго отделена от нуля. Следовательно
\[
\sum_{\gamma\in\Gamma_Y}\int_1^2
 |\zeta(1/2+i(\gamma+v/L))|^2dv\ge c_2Y\log^2Y.
\]
Вместе с (4.3), (5.2), n_Y~YlogY/(2pi) и W(D_m)~3L/4:
\[
\boxed{\frac1{n_Y}\sum_{\gamma\in\Gamma_Y}
             \widetilde G_m[f_{\gamma,m}]\ge a_0L^2,
\qquad a_0>0.}
\tag{5.4}
\]
Это среднее по конкретным единичным векторам ИСХОДНОГО дополнения. Оно не утверждает L^2-рост для каждого f, не заменяет среднее по нулям средним по Лебегу и не предполагает простоту нулей.

## 6. Средний исходный |q_m| на тех же ядрах не превосходит O(L)

### 6.1. Прямое следствие доказанной pair-корреляции

P3, Corollary 1 (6), при RH и любом фиксированном 0<a<1 даёт
\[
\sum_{0<\gamma,\eta\le X}
 \left(\frac{\sin((a/2)(\gamma-\eta)\log X)}
 {(a/2)(\gamma-\eta)\log X}\right)^2
 \frac4{4+(\gamma-\eta)^2}=O(X\log X).
\tag{6.1}
\]
Достаточно a=1/2. На |gamma-eta|<=1/logX оба kernel-фактора отделены от нуля. Поэтому число таких близких ПАР с кратностями есть O(XlogX).

Разобьём (0,3Y] на интервалы длины h=1/log(3Y), пусть n_j — число нулей в j-м интервале с кратностями. Тогда
\[
\sum_jn_j^2=O(Y\log Y).
\tag{6.2}
\]
Для каждого целого k по Cauchy–Schwarz \(\sum_jn_jn_{j+k}\le\sum_jn_j^2\). Поскольку L/log(3Y) ограничено сверху и снизу,
\[
\sum_{\substack{\gamma\in\Gamma_Y\\0<\eta\le3Y}}
 \min\{L^2,|\gamma-\eta|^{-2}\}
\le C L^2\sum_j n_j^2
=O(L^2Y\log Y).
\tag{6.3}
\]
Для вывода достаточно просуммировать по расстоянию k между ячейками с весом O((1+k^2)^(-1)). Большие щели и кратные нули не исключались.

### 6.2. Возврат полной формы, включая все нули

Только внутри RH-ветви полная явная формула даёт
\(\mathfrak k[v]=\sum_\rho|\widehat v(\gamma_\rho)|^2\ge0\).
Это F/source identity плюс RH, не безусловное использование абсолютных квадратов.

Для v=v_(gamma,L):
\[
|\widehat v(\eta)|^2\le2\min\{L^2/4,|\eta-\gamma|^{-2}\}
                           +2(\eta+\gamma)^{-2}.
\tag{6.4}
\]
Вне eta<=3Y первый хвост, по N(x)=O(x log(2+x)), имеет сумму O(logY/Y) для каждого gamma<=Y. Второй член суммируется равномерно при gamma>=1. С учётом обоих знаков ординат (6.3)–(6.4) дают
\[
\sum_{\gamma\in\Gamma_Y}\mathfrak k[v_{\gamma,L}]
\le C L^2 n_Y.
\tag{6.5}
\]
Неоплаченного high-zero tail здесь нет.

Для e=v-P_mv оценки (4.2) и оба endpoint jump masses дают
\[
|\widehat e(t)|\le
\frac{C\gamma L}{\sqrt m(1+|t|)}.
\]
Действительно, отдельно применяются L1-оценка и integration by parts с полной вариацией нулевого продолжения. Поэтому в RH-ветви
\[
\mathfrak k[e]\le C\gamma^2L^2/m,
\qquad
\frac{\mathfrak k[e]}{\|P_mv\|^2}\le C Y^2L/m=o(1).
\tag{6.6}
\]
Положительность нулевой суммы позволяет \(\mathfrak k[P_mv]\le2\mathfrak k[v]+2\mathfrak k[e]\). После деления на \(\|P_mv\|^2\asymp L\), суммирования и (1.2):
\[
\boxed{\frac1{n_Y}\sum_{\gamma\in\Gamma_Y}q_m[f_{\gamma,m}]
\le b_0L.}
\tag{6.7}
\]
Кроме того, q_m[f]>=-B_0 для любого единичного f при RH. Следовательно
\[
\boxed{\frac1{n_Y}\sum_{\gamma\in\Gamma_Y}|q_m[f_{\gamma,m}]|
\le b_0L+2B_0=O(L).}
\tag{6.8}
\]
Вот строгий смысл сравнения L^2 против L. Это не operator-norm bound |q_m|=O(L) на всём carrier.

## 7. RH-ветвь: отрицательный upper для остатка

Из (5.4),(6.7), для каждого фиксированного a>0 и всех достаточно больших m:
\[
\inf_{\substack{f\in J_m^\perp\\\|f\|=1}}
 (q_m[f]-a\widetilde G_m[f])
\le \frac1{n_Y}\sum_\gamma(q_m[f_{\gamma,m}]-a\widetilde G_m[f_{\gamma,m}])
\le b_0L-aa_0L^2\longrightarrow-\infty.
\tag{7.1}
\]
Использован правильный верхний envelope. Не утверждается, что один заранее выбранный gamma работает для всех m. Существование хотя бы одного нарушающего вектора на каждом позднем m следует из отрицательного среднего. Нормировки и проекционные потери уже оплачены.

## 8. Снятие временной RH-предпосылки: безусловный запрет формы доказательства

**[COFINAL_FAMILY | PAPER using inherited S2/S3.]** При not-RH S3 даёт \(\lambda_{\min}(A_m)\to-\infty\). В разложении J_m direct_sum J_m-perp:
\[
A_m=\begin{pmatrix}D&B^*\\B&G\end{pmatrix},\quad
\|D\|,\|B\|\le\delta_m\to0.
\]
Матрица отличается от diag(D,G) на норму <=delta_m. Поэтому, как только полный нижний уровень <-2delta_m,
\[
\lambda_{\min}(G)\le\lambda_{\min}(A_m)+\delta_m\to-\infty.
\]
По (1.2) inf_(J_m-perp) q_m<=lambda_min(G)+B_0. Поскольку \(\widetilde G_m\ge0\), (0.1) следует и в случае not-RH. Вместе с §7 это доказывает (0.1) без RH.

Эквивалентная логика от противного: постоянный остаточный пол => q-floor на дополнении => полный constant floor => RH по S2/S3; но при RH §7 опровергает этот остаточный пол. Это корректная дихотомия, а не использование RH для доказательства RH. Итоговая source-positive задача q_m>=-K не опровергнута.

Ограничение силы результата: здесь не дана численная константа начала m_0 и не исполнен независимый аудит всей новой аналитической цепочки. Импортированные Gonek/Montgomery-теоремы дают существование фиксированных констант, достаточное для cofinal counterexample. Локальные проверки ниже не сертифицируют эту цепочку.

## 9. Необходимая нормировка и то, что она НЕ доказывает

**[COFINAL_FAMILY | PAPER.]** Пусть a_m>=0. Если с одной K на неограниченной семье
\(q_m-a_m\widetilde G_m\ge-K\) на всём J_m-perp, то q_m>=-K и S2/S3 влекут RH. Теперь (5.4),(6.7) дают на этой семье
\[
\boxed{a_m\le\frac{b_0L+K}{a_0L^2}=O(1/L).}
\tag{9.1}
\]
Таким образом, для ПРОПОРЦИОНАЛЬНОГО масштабирования исходных весов \(a_mW(m)=O(1)\) необходимо. Для произвольного перераспределения весов этот вывод автоматически не заявляется.

Естественный ремонт:
\[
\boxed{\bar w_{m,d}=\frac{\Lambda(d)}{dW(m)},\quad
\sum_{d=2}^m\bar w_{m,d}=1,\quad
\bar G_m[f]=\widetilde G_m[f]/W(m).}
\tag{9.2}
\]
При m>=2 знаменатель строго положителен. Положительность, все степени простых, точные floors и полные выходные нормы сохранены. На ансамбле §5 обязательный нижний масштаб становится cL вместо cL^2; это только снятие обнаруженной потери, НЕ верхний bound нормированного lift.

Остаток меняется точно:
\[
\boxed{q_m-\bar G_m=(q_m-\widetilde G_m)
                      +(1-W(m)^{-1})\widetilde G_m.}
\tag{9.3}
\]
Нельзя оставить старый остаток после нормировки. В source-форме S1 §7.6 весь floor-компенсатор и все rational-shift atoms делятся на W(m). Не доказано, что полученный полный остаток ограничен снизу. В частности, суммарный вес 1 не ограничивает по отдельности высоты ζ-пиков или короткий N-сектор.

Outer filtering до d=p,p^2 не спасает ненормированный вариант: удалённый вес \(\sum_{p,k\ge3}(\log p)/p^k\) ограничен, поэтому W_12(D)=logD+O(1); §§3–8 остаются верными с тем же типом констант. Это не удаляет высшие степени из исходного q-return (1.2).

## 10. E / F / LA и точные границы импорта

E — действительные Euler/von-Mangoldt коэффициенты и их положительность; F — конкретная completed-zeta/Weil структура; LA — линейная алгебра, Fourier/окно/нормировка. Как установлено в предыдущем EFZ-аудите, этих трёх ярлыков недостаточно для всей аналитики: ниже A обозначает аналитический импорт, I — ordinary-integer arithmetic; Z — лишь счёт с кратностями.

| Шаг | Классификация | Чего не утверждает |
|---|---|---|
| Определение centered square, Parseval, положительность | E + LA | Не сравнение с q |
| Титчмарш / P1 и Euler–Maclaurin | A + I; не одно абстрактное F | Не uniform expansion при N<|t| |
| W(x)=log x+O(1) | E + I + elementary LA | Не гипотеза о нулях |
| cos(gamma x) и проекция в исходное дополнение | LA + actual nodes определения J | Не eigenvector, не простой нуль |
| Gonek shifted mean | E/F/A theorem, CONDITIONAL RH branch | Не безусловный знак q, не один Z-count |
| Montgomery pair bound | E/F/A theorem, CONDITIONAL RH branch | Не pair-correlation conjecture |
| Полная k-сумма квадратов в §6 | F + A + RH, только внутри ветви | Не использование абсолютных квадратов вне RH |
| Дихотомия и перенос constant floor | LA + inherited S2/S3 | Не доказательство RH |
| Нормировка общей массой и (9.3) | E + LA | Не оплата нового остатка |

Требование доказательства только из положительных коэффициентов E и фиксированного gamma/pole F этим no-go не удовлетворяется: используются указанные аналитические теоремы в условной ветви. Это явно задекларированный способ доказать ПРЕПЯТСТВИЕ, не скрытый нулевой импорт в положительный target.

## 11. Strongest attack, consumer contract, closeout

Сильнейший objection: Gonek conditional on RH не даёт unconditional counterexample. Ответ — §8, проверяющий обе ветви; никакого RH-утверждения из самих moment estimates не выводится. Второй objection: scalar mean не обязан сохраняться в J-perp. Ответ — конкретные f_(gamma,m) из §4 и uniform projection budgets (4.3),(6.6). Третий: q=O(L) неверно на всех направлениях. Такой claim не нужен и не сделан; доказано только среднее (6.8) на том же ансамбле.

DOWNSTREAM_CONSUMER: constant lower floor on the unchanged CCM complement, then the inherited RH implication.
ACTUAL_CONSUMER_REQUIREMENT: q_m>=-K on an unbounded family.
ORIGINAL_REQUESTED_OBJECT: centered divisor positive lift with bounded signed remainder.
ORIGINAL_OBJECT_IS: NOT_NECESSARY; one chosen sufficient representation only.
KILL_SCOPE: THEOREM_SHAPE; fixed positive multiple of the exact unnormalized (1.1), including its outer prime/square-filtered variant.
KILL_EVIDENCE: all-late negative upper (7.1) in the RH branch and §8 in the other branch.
RESEARCH_DEBT: lower bound of q_m-bar G_m or another source-defined normalized weighted residual.
REOPEN_TRIGGER: positive normalized-source certificate with every rational-shift, floor, projection and external-output term retained.
NOVELTY_AXIS: spectral-scale obstruction on actual J_m-perp, not repetition of raw sqrt(N) obstruction.

Two candidate re-representations, before any larger computation:

1. Proportional normalized lift (9.2). Exact object: q_m-bar G_m. Kill power high / moderate finite cost; cofinal lower bound remains separate. A numerical sign near zero requires full error enclosure, not a fit.
2. Nonnegative scale-shell weights with total mass <=1, chosen independently of the unknown sign of q. Exact object: full recomputed rational-atom/floor remainder. Kill power medium-high / moderate coefficient cost. This is a different lift and must not inherit old residual assertions.

DISCRIMINATOR: an upper envelope of q_m-a Gtilde_m on the concrete zero-kernel ensemble for failure; an independent lower envelope for the entire normalized complement for success. A small residual of J itself is neither.

ONE CODEX DIRECTIVE: CENTERED_DIVISOR_SCALE_AUDIT. Independently audit P2's uniform shift substitution, P3's close-pair/bin implication, the two projection budgets and RH-case elimination. Preserve all multiplicities and N=m. Do not ask an eigensolver to replace §§5–8. If these checks pass, archive unnormalized lift as killed only at this theorem shape; test the exact normalized remainder (9.3), not the old one. No route-state or RH export edits.

Progress: FALSIFICATION_PROGRESS. Closed quantifier: no fixed positive unnormalized coefficient can have the required constant remainder on any unbounded original subsequence. Forbidden repeat: centered therefore correctly scaled; ordinary Lebesgue mean therefore mean on complement; normalization therefore same remainder. Normalized target remains open.

## 12. Checks, predictions and delivery

Before local execution, P1–P6 were recorded in registration.json: half-endpoint sign and next coefficient; exact all-prime-power factorial identity; residual normalization identity; vanishing projection exponents at Y=m^(1/4); positive shifted Gonek coefficient; finite 29/14 multiplier checks. Seven local exact-control groups passed. Sixteen 60-digit multiplier samples and nine fixed-t expansion samples were evaluated; these are floating diagnostics, not interval certification. They do not test or prove the new cofinal statement. The code below is included verbatim; it is not a Lean proof or an independent audit.

P1: fixed-t expansion samples agree with +1/2 and converge toward -s/12. P2/P3/P4: exact controls pass. P5: positivity follows analytically from |sin x|<|x| at nonzero x and is numerically sanity-checked. P6: all 16 sample upper checks pass. No retroactive repair of a failed prediction occurred. No CCM eigensystem was computed.

Delivery scope: one NEW Markdown in docs/routeB_bus/proshka/ on proshka_inbox_2026-10-31. Existing verdicts, rh_clean, Lean and route state are not edited. A successful Git write is not analytic verification. Commit SHA is reported only after write/readback; it is not embedded in its own contents. No Lean files, so lake commands and an axiom profile are not applicable.

Primary URLs (reference strings, not additional theorem imports):
```text
P1 https://arxiv.org/abs/2406.16667
Titchmarsh https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf
P2 https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/5-mvzdrvs.pdf
P3 https://www-personal.umich.edu/~hlm/paircor1.pdf
Visual cross-check of P2 https://arxiv.org/abs/2512.03297
```

### Reproducible local controls

```python
"""Local exact controls and floating normalization diagnostics; no RH computation.
Run: uv run --with sympy --with mpmath checks.py
"""
from __future__ import annotations
import json
import math
import sympy as sp
import mpmath as mp

# 1: Exact multiplier convention and complete-square lower bound.
t = sp.symbols('t', real=True)
s = sp.Rational(1,2)-sp.I*t
assert sp.simplify(1-s-(sp.Rational(1,2)+sp.I*t)) == 0
x,y,u,v=sp.symbols('x y u v', real=True)
assert sp.expand((x+u)**2+(y+v)**2-(x*x+y*y)/2+u*u+v*v
                 -((x+2*u)**2+(y+2*v)**2)/2)==0
print('PASS 1 multiplier convention and square lower bound')

# 2: Every prime-power coefficient in log(n!) = sum Lambda(d) floor(n/d).
for n in range(2,49):
    left=sp.factorint(math.factorial(n)); right={}
    for d in range(2,n+1):
        fac=sp.factorint(d)
        if len(fac)==1:
            p=next(iter(fac));right[p]=right.get(p,0)+n//d
    assert left==right
print('PASS 2 factorial-Mangoldt identity, all prime powers')

# 3: Normalization and its remainder cannot be separated.
q,g,w=sp.symbols('q g w', real=True, nonzero=True)
assert sp.simplify((q-g/w)-((q-g)+(1-1/w)*g))==0
weights=[sp.Rational(1,2),sp.Rational(2,3),sp.Rational(3,7)]
assert sum(z/sum(weights) for z in weights)==1
print('PASS 3 normalization and exact residual change')

# 4: The projection powers used in the proof.
a=sp.Rational(1,4)
assert a-sp.Rational(1,2)<0 and 2*a-1<0
assert (a-sp.Rational(3,2))+1==a-sp.Rational(1,2)
print('PASS 4 uniform projection exponent budgets')

# 5: Exact cosine Fourier coefficients with the physical L2 basis.
z=sp.symbols('z', real=True)
gamma=sp.Rational(1,3)
for n in range(1,5):
    lhs=sp.integrate(sp.cos(gamma*z)*sp.cos(n*z),(z,-sp.pi,sp.pi))
    rhs=2*gamma*(-1)**n*sp.sin(sp.pi*gamma)/(gamma**2-n**2)
    assert sp.simplify(lhs-rhs)==0
print('PASS 5 actual cosine projection coefficient')

# 6: Bin-correlation Cauchy inequality, without spacing assumptions.
bins=[1,0,2,4,1,3,0,2]
energy=sum(k*k for k in bins)
for shift in range(len(bins)):
    assert sum(bins[i]*bins[i+shift] for i in range(len(bins)-shift))<=energy
print('PASS 6 bin-pair aggregation control')

# 7: Carrier normalization and two-sided frequency packet convention.
L=sp.symbols('L',positive=True)
gam=sp.symbols('gam',positive=True)
assert sp.simplify(sp.integrate(sp.cos(gam*z)**2,(z,-L/2,L/2))
                   -(L/2+sp.sin(gam*L)/(2*gam)))==0
print('PASS 7 unprojected kernel norm')

# Floating diagnostics are not interval certificates.
mp.mp.dps=60
K=mp.mpf(29)/14
rows=[]
for N in [8,32,128,512]:
    for tv in [mp.mpf(0),mp.mpf(1),mp.mpf(N)/2,mp.mpf(N)]:
        ss=mp.mpf('.5')-1j*tv
        aa=mp.fsum(mp.power(n,-ss) for n in range(1,N+1))-mp.power(N,1-ss)/(1-ss)
        scaled=abs(aa-mp.zeta(ss))*mp.sqrt(N)
        assert scaled<K
        rows.append(dict(N=N,t=str(tv),sqrtN_error=mp.nstr(scaled,18)))
fixed=[]
for tv in [mp.mpf(0),mp.mpf(3),mp.mpf(14)]:
    ss=mp.mpf('.5')-1j*tv
    for N in [64,256,1024]:
        aa=mp.fsum(mp.power(n,-ss) for n in range(1,N+1))-mp.power(N,1-ss)/(1-ss)
        nextcoef=(aa-mp.zeta(ss)-mp.mpf('.5')*mp.power(N,-ss))*mp.power(N,ss+1)
        fixed.append(dict(N=N,t=str(tv),next_coefficient=mp.nstr(nextcoef,18),target=mp.nstr(-ss/12,18)))
assert 1-(mp.sin(mp.mpf(1)/8)/(mp.mpf(1)/8))**2>0
print('PASS floating uniform-bound controls and shifted-coefficient sign')
print(json.dumps({'precision':60,'diagnostic_not_certificate':True,
                  'uniform_bound_samples':rows,'Euler_Maclaurin_samples':fixed},indent=2))

```
