# STATUS: TRY_CCM_HADAMARD_WINDOW_VARIATION
```yaml
OPERATIVE_CLASS: TRY_CCM_HADAMARD_WINDOW_VARIATION
DATE: 2026-11-02
SOURCE_REPO: Malaeu/chen_q3
SOURCE_COMMIT: 36e9555645afa80aaf0560f55a5f2f3fee6b48fe
SOURCE_FILES:
  - docs/NOESCAPE_STORY_2026-10-30.md
  - docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md
  - q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean
SOURCE_NOESCAPE_SHA256: fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded
SOURCE_NOESCAPE_SHA256_PROVENANCE: OWNER_SUPPLIED_NOT_REHASHED_IN_THIS_TURN
SOURCE_NOESCAPE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
SOURCE_MATRIX_N1_GIT_BLOB: 960f1de9d00e9ca4b309a99fe98be48db40cdb31
VERIFIER: PAPER
RESULT: COMPLETE_SOURCE_DERIVATION_OF_FIXED_RANK_WINDOW_VARIATION
SCOPE: FINITE_CELL_AND_ALL_FIXED_N_CONTINUOUS_L
ZERO_LOCATION_ASSUMED: false
CCM_DIMENSION_N_HELD_FIXED_WHILE_DIFFERENTIATING: true
ORIGINAL_DIAGONAL_N_EQUALS_M_L_EQUALS_LOG_M: PRESERVED_AT_EVALUATION
SIMPLE_EIGENVALUE_FORMULA: PROVED_PAPER
MULTIPLE_EIGENVALUE_ONE_SIDED_FORMULA: PROVED_PAPER
PRIME_POWER_RANK_ONE_SLOPE_JUMPS: PROVED_PAPER
NEGATIVE_SLOPE_JUMP_IMPLIES_MONOTONICITY_OR_RH: false
EXACT_SYMBOLIC_CHECKS: FOUR_PASSED
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
REPOSITORY_WRITE: NOT_PART_OF_MATHEMATICAL_CLAIM
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: FIXED_RANK_GEOMETRIC_VARIATION_AND_ARITHMETIC_KINK_THEOREM
ROUTE_SCORE: 4
```

## 0. Результат и пределы

**[FINITE_CELL | PAPER; доказано ниже.]** Для исходного CCM при **фиксированном** числе Fourier-мод `N` и непрерывно меняющейся длине `L>0` определим вещественный чётный блок `K_{N,E}(L)` непосредственно ограничением исходной полной Weil-формы на окно `[-L/2,L/2]`. На открытых интервалах, не содержащих `log n` с `Λ(n)>0`, он является дифференцируемой вещественной симметричной матрицей; при простом нижнем собственном значении

\[
\boxed{\lambda_{N,0}'(L)=c_L^T K_{N,E}'(L)c_L,\qquad
 K_{N,E}(L)c_L=\lambda_{N,0}(L)c_L,\quad\|c_L\|=1.}\tag{0.1}
\]

Вычислена **вся** правая часть: pole/boundary, архимедово ядро, каждый поддержанный prime power. В точке `L_*=log n` матрица и её собственные значения **не прыгают**; при простом bottom его *производная* имеет отрицательный скачок

\[
\boxed{
\lambda_{N,0}'(L_*+)-\lambda_{N,0}'(L_*-)
=-2\frac{\Lambda(n)}{\sqrt n}
\bigl|f_{L_*}(L_*/2^-)\bigr|^2
=-\frac{2\Lambda(n)}{\sqrt n\,L_*}
\left|c_0+\sqrt2\sum_{j=1}^N c_j\right|^2\le0.
}\tag{0.2}
\]

При `n=p^k` коэффициент перед квадратом равен `-2/(k p^{k/2})`. Если `Λ(n)=0` или крайовой след нижнего вектора равен нулю, арифметического скачка наклона нет. Для кратного bottom даётся точная формула через экстремумы сжатого производного оператора, **не** незаконная подстановка произвольного одного собственного вектора.

**[COFINAL_FAMILY | CONDITIONAL.]** Ни (0.1), ни (0.2) не устанавливают RH, NOESCAPE или знак гладкого дрейфа: остаются совместные prime/arch и pole члены и скачок числа мод на исходном диагональном расписании `N=m, L=log m`. Ветка `(★)` не опровергнута одной неудачной амплитудной или фазовой оценкой; доказанная здесь геометрическая вариация является отдельным тестом.

## 1. Неподменённая семья и фиксированная метрика

**[FINITE_CELL | PAPER.]** При фиксированном `N≥0` и произвольном `L>0` положим `b=L/2`, `I_L=[-b,b]` и

\[
\psi_{j,L}(x)=L^{-1/2}e^{2\pi i j(x+b)/L}\mathbf1_{I_L}(x),\qquad |j|\le N.
\]

Это в точности базис NOESCAPE (1.1) при подстановке `N=m`, `L=log m`. Вещественный чётный ортонормированный базис:

\[
e_{0,L}=\psi_{0,L},\qquad
 e_{j,L}=\frac{\psi_{j,L}+\psi_{-j,L}}{\sqrt2}
 =\sqrt{2/L}\cos\bigl(2\pi j(x/L+1/2)\bigr)\mathbf1_{I_L},\ 1\le j\le N.
\tag{1.1}
\]

Отождествим все коэффициентные пространства с фиксированным `R^{N+1}`. Эквивалентная изометрия на фиксированное окно `[-1/2,1/2]` задаётся

\[
\phi_0(t)=1,\quad\phi_j(t)=\sqrt2\cos[2\pi j(t+1/2)],\qquad
\phi_c(t)=\sum_{j=0}^N c_j\phi_j(t),
\]
\[
f_{L,c}(x)=L^{-1/2}\phi_c(x/L)\mathbf1_{I_L}(x),\qquad
\|f_{L,c}\|_{L^2(\mathbb R)}^2=\|c\|_{\ell^2}^2.
\tag{1.2}
\]

Из-за фазового сдвига `+1/2` **концевой вектор** имеет компоненты
\[
v=(\phi_0(1/2),\ldots,\phi_N(1/2))^T
 =(1,\sqrt2,\ldots,\sqrt2)^T,
\quad f_{L,c}(b^-)=L^{-1/2}v^Tc.
\tag{1.3}
\]

Таким образом, производная матрицы определяется **после переноса на одну и ту же коэффициентную метрику**. Дифференцировать выражение с меняющимся физическим пространством, забыв производную базиса, нельзя. Ещё нельзя одновременно дифференцировать `N=⌊e^L⌋`: размерность в этом случае скачет. Мы сначала держим `N` фиксированным, а затем ставим `N=m,L=log m`.

Для исходного источника определим
\[
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\qquad
c_*=\gamma+\log(8\pi)+\pi/2,\qquad a_n=\frac{\Lambda(n)}{\sqrt n}.
\]

Его полная форма (NOESCAPE (1.4)) содержит `-c_*||f||²`, arch-интеграл, `-Σ_{n≥2}a_n Q_f(log n)`, а также положительный чётный полюс `p=√2 cosh(x/2)` и отрицательный нечётный полюс `q=√2 sinh(x/2)`. Последний **равен нулю по чётности**, а не отбрасывается соглашением. Для поддержки длины `L` корреляция при `log n≥L` точно равна нулю; все proper prime powers с `log n<L` остаются.

## 2. Корреляционное ядро и его краевой след

**[FINITE_CELL | PAPER.]** Для `0≤u≤1` положим

\[
\mathcal Q_{ij}(u)=2\int_{-1/2}^{1/2-u}\phi_i(t)\phi_j(t+u)dt,
\qquad \mathcal Q_{ij}(u)=0\ (u≥1).
\tag{2.1}
\]

Благодаря чётности базисных функций это ровно `Q_{e_i,e_j}(s)` при `u=s/L`. В частности, `Q_L(0)=2I`, `\mathcal Q(1)=0`; матрица `\mathcal Q(u)` симметрична. Для `0<u<1`:

\[
\mathcal Q'_{ij}(u)=2\left[
 -\phi_i(1/2-u)\phi_j(1/2)
 +\int_{-1/2}^{1/2-u}\phi_i(t)\phi_j'(t+u)dt
\right].
\tag{2.2}
\]

Первое слагаемое — **строго реальный boundary trace**, второе — внутренний эффект изменения нормированных гармоник. При `u↑1` интеграл обращается в ноль, а `\phi_i(-1/2)=\phi_i(1/2)=v_i`. Получаем

\[
\boxed{\mathcal Q'(1^-)=-2vv^T,\qquad\mathcal Q'(1^+)=0.}\tag{2.3}
\]

Для произвольного `c` диагональная форма `q_c(u):=c^T\mathcal Q(u)c` удовлетворяет
\[
q_c'(u)=2\left[-\phi_c(1/2-u)\phi_c(1/2)
+\int_{-1/2}^{1/2-u}\phi_c(t)\phi'_c(t+u)dt\right],
\quad q_c'(1^-)=-2(v^Tc)^2.
\tag{2.4}
\]

`q_c` непрерывна, кусочно гладкая, с ограниченными односторонними производными; у `u=0` возможен cusp вследствие нулевого продолжения, и он **учтён**. Следовательно `∂_L q_c(s/L)=-(s/L²)q_c'(s/L)` почти всюду, а произведение с `j(s)~1/(2s)` интегрируемо около `s=0`.

## 3. Полюс, исходная архимедова граница и её точное сокращение

**[FINITE_CELL | PAPER.]** Чётный полюс имеет в выбранном базисе вектор

\[
 u_j(L)=\langle e_{j,L},\sqrt2\cosh(x/2)\rangle
 =\frac{4\sqrt2\,d_j L^{3/2}\sinh(L/4)}{L^2+16\pi^2j^2},
 \quad d_0=1,\quad d_j=\sqrt2\ (j≥1).
\tag{3.1}
\]

Значит `W_{0,2}^E(L)=u(L)u(L)^T`. Его производная
\[
\frac{d}{dL}W_{0,2}^E=u'u^T+uu'^T,
\qquad
u_j':=\frac{du_j}{dL}=u_j\left(\frac{3}{2L}+\frac14\coth(L/4)
 -\frac{2L}{L^2+16\pi^2j^2}\right).
\tag{3.2}
\]

Это полный вклад растущего окна от положительного полюса. Нет заранее определённого знака у `2(c·u)(c·u')`.

**Критическая проверка: arch-boundary cancel в буквальных CCM формулах.** Исходная `W_R` (см. `CCMFiniteWeilSourceMatrixN1.lean`, определения `ccmWREntry/ccmQKernel`; тот же source применён после чётного сжатия) имеет вид

\[
 (W_{\mathbb R})_{ij}(L)=\frac{\mathcal Q_{ij}(0)}2
 \bigl[\gamma+\log(4\pi\tanh(L/2))\bigr]
 +\int_0^L\frac{e^{s/2}\mathcal Q_{ij}(s/L)-\mathcal Q_{ij}(0)}
 {e^s-e^{-s}}ds.
\tag{3.3}
\]

Здесь `\mathcal Q(0)=2I` независимо от `L`. У верхней границы `s=L` имеем `\mathcal Q(1)=0`, поэтому
\[
\frac d{dL}\left[\frac{\mathcal Q(0)}2\log\tanh(L/2)\right]
=\frac{\mathcal Q(0)}{2\sinh L},
\]
\[
 \left.\frac{e^{s/2}\mathcal Q(s/L)-\mathcal Q(0)}{e^s-e^{-s}}
 \right|_{s=L}=-\frac{\mathcal Q(0)}{2\sinh L}.
\]

**Они сокращаются точно.** Остаётся только

\[
\boxed{
\frac d{dL}W_{\mathbb R}(L)=
 \int_0^L j(s)\frac{\partial}{\partial L}\mathcal Q(s/L)ds
 =-\frac1{L^2}\int_0^L s j(s)\mathcal Q'(s/L)ds.
}\tag{3.4}
\]

Обмен производной с интегралом обоснован: `\partial_L\mathcal Q(s/L)=O(s/L²)` у `s=0`, а `s j(s)` ограничено; у `s=L` произведение конечное. Нельзя оставлять отдельный ложный surface-term от `\log\tanh(L/2)`.

## 4. Полная производная литерального CCM при фиксированном N

### Теорема 1 (Hadamard–source identity)

**[FINITE_CELL | PAPER; доказано.]** Для `L>0`, не совпадающего с `log n` при `Λ(n)>0`, на фиксированном чётном носителе `N`:

\[
\boxed{
\begin{aligned}
K_{N,E}'(L)={}&u'(L)u(L)^T+u(L)u'(L)^T\\
 &+\frac1{L^2}\int_0^L s j(s)\mathcal Q'(s/L)ds\\
 &+\frac1{L^2}\sum_{\substack{n≥2\\\log n<L}}
      \frac{\Lambda(n)\log n}{\sqrt n}\,
      \mathcal Q'(\log n/L).
\end{aligned}}
\tag{4.1}
\]

**Доказательство.** Определение исходной полной матрицы — `K_{N,E}=W_{0,2}^E-W_{\mathbb R}^E-\mathrm{Prime}^E`, где
\[
 \mathrm{Prime}^E(L)=\sum_{\log n<L}a_n\mathcal Q(\log n/L).
\]

Равенства (3.2) и (3.4) дают первые три члена (4.1). Для конечной суммы (вне порогов) обычное правило цепочки даёт
\[
\frac d{dL}\mathrm{Prime}^E
=-\frac1{L^2}\sum_{\log n<L}a_n(\log n)\mathcal Q'(\log n/L).
\]

Подставляем минус перед `Prime`. При `L=log n` сам новый член равен нулю благодаря `\mathcal Q(1)=0`, поэтому `K` непрерывна; однакo её односторонние производные различаются — §6. Ни один `n=p^k` не выброшен. ∎

### Следствие 2 (буквальная boundary/arch/atom форма)

**[FINITE_CELL | PAPER.]** Для фиксированного `c` определим
\[
D_c(u)=\phi_c(1/2-u)\phi_c(1/2)
-\int_{-1/2}^{1/2-u}\phi_c(t)\phi_c'(t+u)dt.
\]

Поскольку `q_c'(u)=-2D_c(u)`, точная квадратичная производная (4.1) есть

\[
\boxed{
\begin{aligned}
 c^TK_{N,E}'(L)c={}&2(c^Tu)(c^Tu')\\
 &-\frac2{L^2}\int_0^L s j(s)D_c(s/L)ds\\
 &-\frac2{L^2}\sum_{\log n<L}\frac{\Lambda(n)\log n}{\sqrt n}D_c(\log n/L).
\end{aligned}}
\tag{4.2}
\]

Внутри каждого `D_c` первый член — **краевой след**, второй — **внутренний сдвиг**. Первая строка (4.2) — полный чётный полюс. Вторая — полное архимедово ядро, включая точную boundary cancel (3.4). Третья — все активные арифметические атомы. Это разложение не предполагает неотрицательности `D_c` или `c`.

## 5. Формула Адамара для нижнего уровня

### Теорема 3 (simple ground state)

**[FINITE_CELL | PAPER.]** Пусть на открытом промежутке без `log(p^k)` нижний уровень `λ_{N,0}(L)=λ_min K_{N,E}(L)` прост. Тогда можно выбрать нормированный `C¹` коэффициентный вектор `c_L`:
\[
K_{N,E}(L)c_L=\lambda_{N,0}(L)c_L,\qquad c_L^Tc_L=1.
\]

Дифференцирование `λ=c^TKc` даёт
\[
\lambda'=c^TK'c+2(c')^TKc
=c^TK'c+2\lambda(c')^Tc=c^TK'c.
\]

В частности, с `\phi=\phi_{c_L}`, `P_L=c_L^Tu(L)` и `\dot P_L=c_L^Tu'(L)` **при фиксированном в момент дифференцирования `c_L`**, полная формула:

\[
\boxed{
\begin{aligned}
\lambda'_{N,0}(L)={}&2P_L\dot P_L
+\frac1{L^2}\int_0^L s j(s)q'_{c_L}(s/L)ds\\
&+\frac1{L^2}\sum_{\log n<L}
\frac{\Lambda(n)\log n}{\sqrt n}q'_{c_L}(\log n/L).
\end{aligned}}
\tag{5.1}
\]

Нормировка и изменение физического базиса уже оплачены в (1.2), производная `c_L` законно сократилась по собственному уравнению. При отсутствии простоты нельзя использовать формулу с произвольно выбранным одним `c_L`; см. §7. ∎

## 6. Prime-power пороги: непрерывная λ, отрицательный скачок её наклона

### Теорема 4 (точный атомный скачок)

**[FINITE_CELL | PAPER; без RH, без положительности оператора.]** Пусть `L_*=log n` (`n≥2`). В момент пересечения нового атома `q_n=Λ(n)/sqrt n`:

\[
\boxed{K_{N,E}(L_*+)=K_{N,E}(L_*-),}
\tag{6.1}
\]
\[
\boxed{
 K'_{N,E}(L_*+)-K'_{N,E}(L_*-)
 =-\frac{2\Lambda(n)}{\sqrt n\,L_*}\,vv^T
 \preceq0.
}
\tag{6.2}
\]

**Доказательство.** `\mathcal Q(1)=0` даёт (6.1). Архимедов член и `u,u'` непрерывны, все старые атомы гладкие. Входящий атом даёт по (4.1)
\[
\frac{\Lambda(n)}{\sqrt n}\frac{L_*}{L_*^2}\mathcal Q'(1^-)
 =-\frac{2\Lambda(n)}{\sqrt n\,L_*}vv^T.
\]

Здесь `Λ(n)≥0`, поэтому это отрицательный полупорядок. При `Λ(n)=0` (не prime power) скачок нулевой. Никакого Dirac-скачка **самой** `K` или `λ` нет: Dirac-масса появляется лишь во **второй распределительной производной** матрицы, с коэффициентом (6.2). ∎

Если нижний уровень при `L_*` прост, собственный вектор можно непрерывно продолжить через порог. Из (6.2) и (1.3):

\[
\boxed{
\begin{aligned}
\lambda'_{N,0}(L_*+)-\lambda'_{N,0}(L_*-)
 &=-\frac{2\Lambda(n)}{\sqrt n\,L_*}|v^Tc_*|^2\\
 &=-2\frac{\Lambda(n)}{\sqrt n}
 |f_{L_*,c_*}(L_*/2^-)|^2.
\end{aligned}}
\tag{6.3}
\]

При `n=p^k` это
\[
\boxed{\Delta\lambda'=-\frac{2}{k p^{k/2}}
\left|c_{*,0}+\sqrt2\sum_{j=1}^N c_{*,j}\right|^2.}
\tag{6.4}
\]

Это **необязательно строго** отрицательно: eigenvector может иметь нулевой граничный след. Шаг относится к `d/dL` при `N` фиксированном и `L_*` конечном, не к прямому изменению `m` в `N=m`.

## 7. Кратность: правильная односторонняя производная, не скрытая простота

### Теорема 5

**[FINITE_CELL | PAPER.]** Для произвольного `L_*` пусть `E` — ортогональный проектор на всё нижнее собственное пространство `K_{N,E}(L_*)`, а `K'_-`, `K'_+` — матричные односторонние производные (существуют по §4). Тогда существуют производные нижнего уровня с соответствующих сторон:

\[
\boxed{
\lambda'_{N,0}(L_*+)=\lambda_{\min}(E K'_+E|_{\mathrm{Ran}E}),
\qquad
\lambda'_{N,0}(L_*-)=\lambda_{\max}(E K'_-E|_{\mathrm{Ran}E}).
}
\tag{7.1}
\]

**Доказательство.** Конечномерное спектральное возмущение даёт собственные значения у нижнего кластера вида `λ_*+h μ_j+o(|h|)`, где `μ_j` — собственные значения сжатия `E K'_{sign(h)} E`; отделённые верхние уровни не меняют первый порядок. При `h>0` минимум соответствует `min μ_j`, при `h<0` — `max μ_j`. Это даёт (7.1). Кратное нижнее пространство не заменяется выбранным на глаз вектором. ∎

На prime-power пороге `E(K'_+-K'_-)E=-(2Λ(n)/(sqrt n L_*))(Ev)(Ev)^T`, однако разность числовых односторонних производных **не обязана равняться** одному Rayleigh-значению этого ранга-один слагаемого. Если внизу есть пересечение ветвей, cusp может существовать даже без нового prime-power атома.

## 8. Что это говорит о буквальном расписании N=m, L=log m

**[COFINAL_FAMILY | PAPER; exact finite-cell algebra.]** Для каждого целого `m≥2` законно подставить `N=m,L=log m` в доказанные конечномерные формулы. Но дискретный переход к следующей ячейке меняет **два** параметра. Обозначив `λ_N(L)=λ_min K_{N,E}(L)`, получаем тождество

\[
\begin{aligned}
&\lambda_{m+1}(\log(m+1))-\lambda_m(\log m)\\
&=\underbrace{\lambda_{m+1}(\log(m+1))-\lambda_m(\log(m+1))}_{\le0\text{ по min--max, добавлена одна мода}}
 +\underbrace{\int_{\log m}^{\log(m+1)}\lambda_m'(L)dL}_{\text{дрейф фиксированного блока}}.
\end{aligned}
\tag{8.1}
\]

`λ_m` локально Lipschitz (конечномерная непрерывная кусочно-`C¹` матрица), поэтому интеграл понимается через a.e. производную; возможная кратность не мешает. На открытом промежутке `(log m,log(m+1))` нет нового целого n, так что именно там арифметических порогов нет. При фиксированном правом конце две Fourier-системы вложены. Следовательно первый член ≤0, но **второй не имеет доказанного знака**. Из отрицательности атомных скачков наклона нельзя сделать вывод о монотонности самой `λ_m` или о RH. Это и есть точное место, где новая геометрия должна встретить источник.

### Consumer-first ledger

**[ABSTRACT | PAPER/CONDITIONAL.]** DOWNSTREAM_CONSUMER: bound/retention для исходных bottoms, далее RH. ACTUAL_CONSUMER_REQUIREMENT: кванторная спектральная/арифметическая оценка на диагональном расписании, не одна производная. ORIGINAL_REQUESTED_OBJECT: Hadamard variation of `λ_min` for continuous `L`. ORIGINAL_OBJECT_IS: PROVED for source-faithful fixed-`N` interpolation, **not** a differentiable curve with `N=e^L`. KNOWN_WEAKER_INTERFACES: signed window drift plus carrier-insertion min--max (8.1), но они не закрывают RH. FAILURE_TYPE: NO_DERIVATION для cofinal sign/anti-escape, не для формулы вариации. EPISTEMIC_STATUS: RESEARCH_DEBT. NOVELTY_AXIS: SOURCE_WINDOW_SHAPE_DERIVATIVE_WITH_NEGATIVE_RANK_ONE_PRIME_KINK. REOPEN_TRIGGER: доказанная интегральная верхняя/нижняя граница гладкого дрейфа, совместимая с эффектом mode insertion. DISCRIMINATOR: source-specific comparison of `2P_L dot P_L + arch + active-prime` over each `(log m,log(m+1))`, retaining mixed terms.

## 9. Exact-symbolic algebra replay

**[FINITE_CELL | PAPER; verification of factors, not a cofinal test.]** For `N=0`, `q(u)=2(1-u)` and `u_0(L)^2=32sinh²(L/4)/L`. Equation (5.1) reduces to

\[
\boxed{
\lambda_0'(L)=\frac d{dL}\frac{32\sinh^2(L/4)}L
 -\frac2{L^2}\int_0^L s j(s)ds
 -\frac2{L^2}\sum_{\log n<L}\frac{\Lambda(n)\log n}{\sqrt n}.
}
\tag{9.1}
\]

`N=0` is an exact algebraic control, **not** the claimed original diagonal schedule. For `N=1`, the matrix `\mathcal Q(u)` in the source-shifted even basis is
\[
\mathcal Q(u)=\begin{pmatrix}
2(1-u)&-\frac{\sqrt2}{\pi}\sin(2\pi u)\\
-\frac{\sqrt2}{\pi}\sin(2\pi u)&2(1-u)\cos(2\pi u)-\frac1\pi\sin(2\pi u)
\end{pmatrix},\quad 0\le u\le1.
\]

The four exact algebraic controls are: `Q(0)=2I`, `Q(1)=0`, `Q'(1^-)=-2vv^T`, and `d/dL log tanh(L/2)=1/sinh L`. The following runnable script passes those checks; it does **not** certify RH, numerical spectral flow, or a Lean theorem:

```python
import sympy as sp
u, L = sp.symbols('u L', positive=True)
a = sp.sqrt(2) * sp.sin(2 * sp.pi * u) / sp.pi
Q = sp.Matrix([
    [2 * (1-u), -a],
    [-a, 2*(1-u)*sp.cos(2*sp.pi*u) - sp.sin(2*sp.pi*u)/sp.pi],
])
v = sp.Matrix([1, sp.sqrt(2)])
assert (Q.subs(u, 0) - 2*sp.eye(2)).applyfunc(sp.simplify) == sp.zeros(2)
assert Q.subs(u, 1).applyfunc(sp.simplify) == sp.zeros(2)
assert (Q.diff(u).subs(u, 1) + 2*v*v.T).applyfunc(sp.simplify) == sp.zeros(2)
assert sp.simplify(sp.diff(sp.log(sp.tanh(L/2)), L) - 1/sp.sinh(L)) == 0
print('4 exact algebraic checks: PASS')
```

Run with `uv run --with sympy script.py` after saving the snippet as `script.py`. Here `u` is the *dimensionless displacement* `s/L`, `L` is window length; replace nothing but the script filename when needed.

## 10. Predictions, strongest attack, research log, next directive

Predictions registered before algebraic verification: P1 — Q's endpoint derivative is rank-one and negative; P2 — the `log tanh` derivative cancels the explicit arch-integral endpoint; P3 — an entrant prime-power produces a *slope*, not an eigenvalue, jump; P4 — varying `N=⌊e^L⌋` spoils the simple derivative. P1–P2 confirmed by exact symbolic/analytic check; P3 by (2.3),(4.1),(6.2); P4 by the dimension audit and (8.1). No outcomes repaired retroactively.

**STRONGEST ATTACK:** The physical domain varies and the lower eigenvalue might be multiple. Repair: fixed-coefficient isometry (1.2) pays the metric/basis derivative; (7.1) pays multiplicity. No assumption of global eigenvector differentiability or strict negativity at an atom is made. Neither the no-escape conclusion nor any monotonicity assertion is imported.

Sources actually read: `docs/NOESCAPE_STORY_2026-10-30.md` §2 (conceptual geometry/basis), `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md` §1 (literal source, exact basis/full form), both at commit `36e9555645afa80aaf0560f55a5f2f3fee6b48fe`; `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean` `ccmQKernel`, `ccmW02Entry`, `ccmWREntry`, `ccmPrimeEntryN1` at that commit (formula check; **pilot N=1 not a family proof by Lean**). Protocol read at `rh_clean`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Used ordinary finite-dimensional spectral perturbation, direct source calculation and exact symbolic checks. No external theorem about distribution of primes or location of zeta zeros was imported.

Abandoned shortcuts: standard Dirichlet-boundary Hadamard formula `−||∂_n f||²` (incorrect domain/normalization); assuming `K` jumps at `log n` (`Q(1)=0`); assuming simple ground states; and reading `λ_m(log m)` as differentiable in `m` despite dimension changes. Those shortcuts are not licensed by the sources.

Two alternative representations if a future sign bound is sought: (A) physical `D_c(u)` boundary/shift-correlation (4.2), kill-power high / cost high (retains all prime powers); (B) direct finite matrix `u'u^T+uu'^T` plus smooth arch and prime matrix (4.1), kill-power medium-high / cost medium (interval one-sided estimates). Neither is claimed to solve RH.

**SINGLE CODEX DIRECTIVE — READ-ONLY AUDIT OF CCM HADAMARD:** Independently derive `Q'(1^-)=-2vv^T`, `W_R'` boundary cancellation, and the sign/factor in (6.2) from the exact source at `36e9555`. Check the simple/multiple eigenvalue split, especially the direction of the **left** derivative in (7.1). Verify (8.1) against the source carrier inclusion and the prime cutoff at both endpoints. Return `HADAMARD_PAPER_CONFIRMED` or the first explicit incorrect equality with exact source line; no RH claim or Lean/route-state modifications.

**META CLOSEOUT:** closed — full finite-rank source shape derivative and signed atom kink; not closed — joint arithmetic sign of integrated drift and fixed-jet no-escape. No generic amplitude or phase majorant is claimed. Memory entry: `HADAMARD_FIXED_N: smooth window drift + negative prime-power slope kinks; diagonal N=m needs separate mode insertion; no RH inference.`
