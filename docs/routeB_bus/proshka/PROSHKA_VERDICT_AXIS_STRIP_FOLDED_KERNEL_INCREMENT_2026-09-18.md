# STATUS: TRY_EXACT_AXIS_STRIP_KERNEL_WITH_NORMALIZATION_REPAIR
```yaml
OPERATIVE_CLASS: TRY_EXACT_AXIS_STRIP_KERNEL_WITH_NORMALIZATION_REPAIR
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-18
SCOPE: ABSTRACT
VERIFIER: PAPER
EVIDENCE_STATE: ANALYTIC_PROOFS_WITH_EXECUTED_EXACT_ALGEBRA_CONTROLS
REQUESTED_IDENTITY: REPAIRED_FACTOR_ONE_QUARTER_NOT_ONE_HALF
AXIS_IDENTITY: PAPER_PROVED
STRIP_IDENTITY: PAPER_PROVED
AXIS_LIMIT_H_OVER_SIGMA: FOUR_TIMES_LAGUERRE_EXPRESSION
FOLDED_ONE_ATOM_INCREMENT: PAPER_PROVED
FOLDED_VS_CONTOUR_HEAD: DISTINCT_WITH_EXACT_SEAM_CORRECTION
SOURCE_PIN: 7f69355b632d659c1d55cf7780fc871f4f57e963
SOURCE_EULERHB_BLOB: 0c760416b740380c526a0c21dad4737d58ba5940
SOURCE_ENCLOSURE_BLOB: 796f1cb127b3b9d2caeff01e25d5c10f33a3fc61
SOURCE_ENCLOSURE_SHA256_PREFIX_SUPPLIED_BY_OWNER: 5af1cf1a
SOURCE_FULL_SHA256_RECOMPUTED_THIS_ROUND: false
SECONDARY_FINDING: KILL_HALF_COEFFICIENT_FOR_FULL_LINE_KERNEL
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXACT_NEGATIVE_RESIDUAL
KILL_EVIDENCE_REF: SECTION_1_GAUSSIAN_AT_TAU_ZERO
GLOBAL_SIGN_PROVED: false
FOURIER_INCREMENT_NONNEGATIVE_PROVED: false
THETA_NEGATIVE_WITNESS: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
LEAN_KERNEL_CHECKED: false
LEAN_FILES_CHANGED: false
THETA_NUMERICAL_GRID_RUN: false
INDEPENDENT_REVIEW: PENDING
COGNITIVE_OPERATOR: UNIT_AUDIT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
ROUTE_SCORE: 4
CODEX_DISPATCHED: false
PRODUCTION_STATE_CHANGED: false
```

Ы. Запрошенные тождества доказаны ниже с одной необходимой поправкой: при обоих интегралах по всей вещественной прямой коэффициент осевого тождества равен **1/4**, не 1/2. Интегральное представление пока не является положительной суммой квадратов.

## 0. Источники, определения и условия

[ABSTRACT][PAPER] Через GitHub-коннектор прочитан действующий `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`, включая завершающий протокол. Прочитаны необходимые места следующих двух источников на SOURCE_PIN:

- `docs/routeB_bus/proshka/PROSHKA_OWNERDIRECT_GOAL058_EULERHB_2026-09-17.md`, в частности раздел «Где теперь действительно искать положительный квадрат», формула (6).
- `docs/routeB_bus/proshka/PROSHKA_FOLDED_FULL_SOURCE_CONTOUR_ENCLOSURE_2026-09-17.md`, §§1–3, формулы (1.1), (2.5), (3.3), (3.5).

Git blob источников получены от коннектора. Полный SHA-256 исходного enclosure в этом раунде не пересчитан; сообщённый владельцем префикс не выдается за самостоятельную проверку байтов. Попытка прямого скачивания в контейнер не удалась из-за DNS; чтение через GitHub-коннектор состоялось.

[ABSTRACT][PAPER] Все неназванные пределы интегрирования ниже — вся прямая R. Используются обычные производные по указанной переменной. Достаточные условия для осевого тождества:

\[
\int_{\mathbb R}(1+t^2)|\Phi(t)|dt<\infty.
\]

Для полосных тождеств дополнительно предполагаем, что Phi вещественна и чётна, и для каждого необходимого b>0

\[
\int_{\mathbb R}(1+t^2)e^{b|t|}|\Phi(t)|dt<\infty.
\tag{0.1}
\]

Настоящий theta-источник и все конечные сложенные суммы ниже удовлетворяют этим условиям. В них не дифференцируется излом phi_n(|t|) по t: дифференцирование преобразований идет по p или tau.

Фиксируем

\[
j(\tau)=\int\Phi(t)e^{i\tau t}dt,\qquad
F(p)=\int\Phi(t)e^{pt}dt,\qquad
\mathcal H(p)=4\Re(F'(p)\overline{F(p)}).
\]

Для полного источника F(p)=xi(1/2+p). Для вещественной чётной Phi функция j вещественна на R. Конвенция Фурье в источниках: hat f(omega)=integral f(x)exp(-i omega x)dx. У вещественных чётных ядер знак экспоненты не меняет преобразования.

## 1. Осевое тождество: коэффициент 1/4

[ABSTRACT][PAPER] Пусть

\[
K(v)=\int\Phi\!\left(\frac{v+w}{2}\right)
          \Phi\!\left(\frac{v-w}{2}\right)w^2dw.
\]

Тогда

\[
\boxed{
j'(\tau)^2-j(\tau)j''(\tau)
=\frac14\int e^{i\tau v}K(v)dv.
}
\tag{1.1}
\]

Для самой алгебры (1.1) чётность не нужна; она нужна для последующей вещественной полосной интерпретации.

Доказательство. Дифференцирование под интегралом и Фубини дают

\[
j'^2-jj''=\iint(y^2-xy)\Phi(x)\Phi(y)e^{i\tau(x+y)}dxdy.
\]

Симметризация по x,y:

\[
y^2-xy\ \longmapsto\ \frac{x^2+y^2-2xy}{2}
=\frac{(x-y)^2}{2}.
\]

Положим v=x+y, w=x-y. Обратная замена имеет вид x=(v+w)/2, y=(v-w)/2, и

\[
\left|\det\frac{\partial(x,y)}{\partial(v,w)}\right|=\frac12.
\]

Поэтому первый множитель 1/2 от симметризации умножается на второй 1/2 от якобиана. Это доказывает (1.1). Абсолютная интегрируемость обеспечена (x-y)^2<=2x^2+2y^2 и моментным условием.

[FINITE_CELL][PAPER] Независимый точный контроль: Phi(t)=exp(-t^2). Тогда

\[
j(\tau)=\sqrt\pi e^{-\tau^2/4},\quad
j'^2-jj''=\frac\pi2e^{-\tau^2/2},\quad
K(v)=\sqrt{2\pi}e^{-v^2/2}.
\]

Следовательно, integral exp(i tau v)K(v)dv=2pi exp(-tau^2/2). При tau=0 остаток предложенной формулы с коэффициентом 1/2 равен -pi/2<0. Это опровержение только неверной нормировки. При интегрировании по v>=0 для вещественной чётной Phi эквивалентно верна формула

\[
j'^2-jj''=\frac12\int_0^\infty K(v)\cos(\tau v)dv.
\]

## 2. Тождество в полосе в исходных координатах

[ABSTRACT][PAPER] Сохраняем буквальное ядро источника:

\[
K_\sigma(w)=\int v\sinh(2\sigma v)\Phi(v+w)\Phi(v-w)dv.
\]

При p=sigma+i tau, sigma>0:

\[
\boxed{
\frac{\mathcal H(\sigma+i\tau)}{\sigma}
=8\int\cos(2\tau w)
  \left[\int v\frac{\sinh(2\sigma v)}{\sigma}
             \Phi(v+w)\Phi(v-w)dv\right]dw.
}
\tag{2.1}
\]

Доказательство. Из вещественности Phi

\[
\mathcal H(p)=4\iint x\Phi(x)\Phi(y)
 e^{\sigma(x+y)}\cos(\tau(x-y))dxdy.
\]

После симметризации x заменяется на (x+y)/2. Замена x=v+w,y=v-w имеет якобиан 2. Получаем

\[
\mathcal H(p)=8\iint v e^{2\sigma v}
 \Phi(v+w)\Phi(v-w)\cos(2\tau w)dv dw.
\]

При фиксированном w произведение Phi(v+w)Phi(v-w) чётно по v. Поэтому вклад v cosh(2 sigma v) равен нулю, а v exp(2 sigma v) заменяется на v sinh(2 sigma v). Это доказывает (2.1) и совпадает с исходной формулой H=8 hat K_sigma(2 tau).

## 3. Единая нормировка оси и полосы

[ABSTRACT][PAPER] Чтобы не смешать K с нулевым значением K_sigma при sigma=0, введём явно нормированное ядро

\[
\mathscr K_\sigma(v):=\frac4\sigma K_\sigma(v/2)
=\int\frac{w\sinh(\sigma w)}{\sigma}
       \Phi\!\left(\frac{v+w}{2}\right)
       \Phi\!\left(\frac{v-w}{2}\right)dw.
\tag{3.1}
\]

Последнее равенство использует чётность Phi. Тогда

\[
\boxed{\frac{\mathcal H(\sigma+i\tau)}{\sigma}
=\int e^{i\tau v}\mathscr K_\sigma(v)dv.}
\tag{3.2}
\]

Поскольку w sinh(sigma w)/sigma -> w^2,

\[
\mathscr K_0(v):=K(v),\qquad
\lim_{\sigma\to0}\frac{K_\sigma(w)}{\sigma}
=2\int v^2\Phi(v+w)\Phi(v-w)dv=\frac14K(2w).
\]

Доминирование при |sigma|<=b следует из |sinh x|<=|x|exp(|x|) и (0.1); оно дает сходимость нормированных ядер в L1. Поэтому

\[
\boxed{
\lim_{\sigma\to0}\frac{\mathcal H(\sigma+i\tau)}{\sigma}
=\int e^{i\tau v}K(v)dv
=4\bigl(j'(\tau)^2-j(\tau)j''(\tau)\bigr).
}
\tag{3.3}
\]

Независимая проверка: H(i tau)=0 и

\[
\partial_\sigma\mathcal H=4\left(|F'|^2+\Re(F''\bar F)\right).
\]

На оси F=j, F'=-i j', F''=-j'', что снова дает (3.3).

## 4. Приращение при добавлении ровно одного сложенного theta-горба

[ABSTRACT][PAPER] Пусть

\[
a_n=\pi n^2,\qquad
\phi_n(r)=(4a_n^2e^{9r/2}-6a_ne^{5r/2})e^{-a_ne^{2r}},\quad r\ge0,
\]

\[
\Phi_N^{fold}(t)=\sum_{n=1}^N\phi_n(|t|),\qquad m=N+1.
\]

Для r,s>=0 обозначим полностью явную добавку

\[
\boxed{
D_{N,m}(r,s)=
\sum_{n=1}^N\left[\phi_n(r)\phi_m(s)+\phi_m(r)\phi_n(s)\right]
+\phi_m(r)\phi_m(s).
}
\tag{4.1}
\]

Это точное равенство (A+a)(B+b)-AB=Ab+aB+ab, а не оценка.

### 4.1. Осевое ядро

Если K_N определено как K с Phi_N^{fold} вместо Phi, то

\[
\boxed{
\Delta K_N(v):=K_{N+1}(v)-K_N(v)
=\int w^2\left\{
\sum_{n=1}^N\left[
\phi_n\!\left(\left|\frac{v+w}{2}\right|\right)
\phi_{N+1}\!\left(\left|\frac{v-w}{2}\right|\right)
+
\phi_{N+1}\!\left(\left|\frac{v+w}{2}\right|\right)
\phi_n\!\left(\left|\frac{v-w}{2}\right|\right)
\right]
+
\phi_{N+1}\!\left(\left|\frac{v+w}{2}\right|\right)
\phi_{N+1}\!\left(\left|\frac{v-w}{2}\right|\right)
\right\}dw.
}
\tag{4.2}
\]

То есть при r_+=|(v+w)/2|, r_-=|(v-w)/2| это integral w^2 D_{N,N+1}(r_+,r_-)dw. После интегрирования два смешанных члена равны заменой w -> -w. Поэтому также

\[
\Delta K_N(v)=2\sum_{n=1}^N\int w^2\phi_n(r_+)\phi_{N+1}(r_-)dw
+\int w^2\phi_{N+1}(r_+)\phi_{N+1}(r_-)dw.
\tag{4.3}
\]

### 4.2. Исходное полосное ядро

\[
K_{\sigma,N}(w)=\int v\sinh(2\sigma v)
 \Phi_N^{fold}(v+w)\Phi_N^{fold}(v-w)dv.
\]

Тогда

\[
\boxed{
\Delta K_{\sigma,N}(w)
=\int v\sinh(2\sigma v)
 \left\{\sum_{n=1}^N\left[
 \phi_n(|v+w|)\phi_{N+1}(|v-w|)
 +\phi_{N+1}(|v+w|)\phi_n(|v-w|)
 \right]
 +\phi_{N+1}(|v+w|)\phi_{N+1}(|v-w|)
 \right\}dv.
}
\tag{4.4}
\]

Для sigma>0 его нормированная версия получается делением веса на sigma. Два смешанных интеграла в (4.4) равны заменой v -> -v; самовклад не удваивается.

### 4.3. Та же добавка в единой нормировке

\[
\boxed{
\Delta\mathscr K_{\sigma,N}(v)
=\int\frac{w\sinh(\sigma w)}{\sigma}
 D_{N,N+1}\!\left(\left|\frac{v+w}{2}\right|,
                   \left|\frac{v-w}{2}\right|\right)dw.
}
\tag{4.5}
\]

При sigma=0 используется вес w^2, и (4.5) переходит в (4.2). Если H_N^{fold}=4 Re((F_N^{fold})' conjugate(F_N^{fold})), то

\[
\boxed{
\frac{\mathcal H_{N+1}^{fold}-\mathcal H_N^{fold}}{\sigma}
=8\int\cos(2\tau w)\frac{\Delta K_{\sigma,N}(w)}{\sigma}dw
=\int e^{i\tau v}\Delta\mathscr K_{\sigma,N}(v)dv.
}
\tag{4.6}
\]

### 4.4. Коэффициенты произведений без сокращений

Для любого n,m и r,s>=0:

\[
\begin{aligned}
\phi_n(r)\phi_m(s)
={}&e^{-a_ne^{2r}-a_me^{2s}}\bigl[
16a_n^2a_m^2e^{9(r+s)/2}
-24a_n^2a_me^{(9r+5s)/2}\\
&\hspace{30mm}-24a_na_m^2e^{(5r+9s)/2}
+36a_na_me^{5(r+s)/2}\bigr].
\end{aligned}
\tag{4.7}
\]

Подстановка m=N+1 даёт полностью раскрытый смешанный член; подстановка n=m=N+1 — самовклад. Оба отрицательных коэффициента сохранены.

[COFINAL_FAMILY][PAPER] Так как phi_n(r)=2a_ne^{5r/2}(2a_ne^{2r}-3)e^{-a_ne^{2r}}>0 на r>=0, сложенные суммы возрастают к полной Phi. Ядра K_N и mathscr K_{sigma,N} возрастают поточечно к соответствующим полным ядрам и сходятся в L1 при фиксированном sigma; на ограниченных sigma применяется (0.1). Это оправдывает точное телескопирование суммы приращений. Положительность отдельных преобразований приращений этим не установлена.

## 5. Связь с формулой (3.3) источника: два разных конечных объекта

[ABSTRACT][PAPER] Для сложенного источника

\[
F_N^{fold}(p)=2\sum_{n=1}^N\int_0^\infty\phi_n(t)\cosh(pt)dt.
\]

Преобразование добавленного горба равно

\[
A_m(p):=F_{N+1}^{fold}(p)-F_N^{fold}(p)
=I_m(p,0)+I_m(-p,0).
\]

Формула (3.3) указанного источника, в том числе при theta=0 по прямой подстановке в исходный интеграл, даёт

\[
I_m(p,\theta)=a_m^{-p/2-1/4}
\left[(p-1/2)\Gamma(b,z)+2z^be^{-z}\right],
\qquad b=p/2+5/4,\quad z=a_me^{2i\theta}.
\]

Gamma(b,z) — верхняя неполная гамма-функция; ветвь та же, что в источнике. Независимый контроль на стороне преобразований:

\[
\mathcal H_{N+1}^{fold}-\mathcal H_N^{fold}
=4\Re\left((F_N^{fold})'\bar A_m+A_m'\overline{F_N^{fold}}+A_m'\bar A_m\right).
\tag{5.1}
\]

На оси, если r_m(tau)=A_m(i tau), то

\[
L_{N+1}-L_N=2j_N'r_m'-j_Nr_m''-r_mj_N''+(r_m'^2-r_mr_m'')
=\frac14\int e^{i\tau v}\Delta K_N(v)dv.
\tag{5.2}
\]

При ненулевом угле контурная голова источника — другой объект:

\[
J_N(p;\theta)=\sum_{n\le N}[I_n(p,\theta)+I_n(-p,-\theta)].
\]

Её связь со сложенным преобразованием точно оплачена формулой (3.5) источника:

\[
\boxed{
J_N(p;\theta)=F_N^{fold}(p)
-\int_0^{i\theta}[g_N(z)-g_N(-z)]e^{pz}dz,
\qquad g_N=\sum_{n\le N}\phi_n.
}
\tag{5.3}
\]

Приращение контурной головы равно A_m минус тот же вертикальный интеграл с g_N, заменённым на phi_m. Формулы (4.2)–(4.6) относятся именно к Phi_N^{fold}, а не автоматически к контурному h_N. Абсолютные значения действительных координат не аналитически продолжаются.

## 6. Граница знака и обязательных нулей

[ABSTRACT][PAPER] Квадрат w^2 внутри интеграла не является квадратом модуля преобразования. Даже при положительной Phi из K>=0 и Delta K_N>=0 не следует неотрицательность их преобразований Фурье.

Точный гладкий контроль этого различия: пусть g(t)=pi^{-1/2}exp(-t^2) и

\[
\Phi_*(t)=2g(t)+\frac{g(t-4)+g(t+4)}2>0.
\]

Это вещественный чётный быстро убывающий источник. Его преобразование j_*(tau)=exp(-tau^2/4)(2+cos(4 tau)) удовлетворяет

\[
\boxed{(j_*'^2-j_*j_*'')(\pi/4)=-\frac{31}{2}e^{-\pi^2/32}<0.}
\]

Это не theta-контрпример. Он показывает ровно то, что интегральное тождество для положительного источника само по себе не есть искомая положительная факторизация.

При j(gamma)=0:

\[
(j'^2-jj'')(\gamma)=j'(\gamma)^2.
\]

В простом вещественном нуле это строго положительно, а не равно нулю. Обязательное обнуление здесь возникает в кратном нуле. Для исходной H вся ось sigma=0 даёт ноль по отражению; после деления на sigma остаётся нетривиальный предел (3.3).

## 7. Closeout и точный следующий интерфейс

[ABSTRACT][PAPER] Задача этого раунда — тождества, не глобальная положительность. Все три запрошенных вычисления выполнены; неверный коэффициент 1/2 явно заменён на 1/4 с точным отрицательным контролем. Новые сетки настоящего theta-источника не запускались. Lean не запускался.

Регистрация перед символьными контролями: P_JACOBIAN=0.99, P_AXIS_STRIP=0.99, P_INCREMENT=0.99. Все три предсказания CONFIRMED. Исполнен `python check_identities.py`: якобиан, симметризация, гауссовский контроль, осевой предел, полный трёхчленный инкремент и коэффициенты (4.7) прошли точные проверки SymPy. Это контроль алгебры, не автоматическая проверка аналитических гипотез.

[COFINAL_FAMILY][CONDITIONAL] Для остающегося знака сохраняются два кандидата, не новые доказанные требования:

- R1: построить из полной Phi автокорреляционное представление mathscr K_sigma=integral h_{sigma,a}*tilde h_{sigma,a} dnu(a), nu>=0, с законной сходимостью. Тогда H/sigma=integral |hat h_{sigma,a}|^2 dnu>=0. Решающее действие 10/10, ожидаемая сложность построения 8/10.
- R2: сохранять весь подписанный телескопический Fourier-ряд приращений и доказать нижнюю оценку его полных частичных сумм с исчезающей ошибкой, не требуя знака каждого инкремента. Решающее действие 9/10, алгебраическая стоимость 2/10, глобальная аналитическая стоимость пока неизвестна.

Это исследовательские оценки стоимости, не вероятности. DISCRIMINATOR для нуль-согласованного результата: точный дефект предложенной факторизации и нижняя/верхняя оболочка полной H/sigma, а не знак K в координатах.

K8A:

```yaml
DOWNSTREAM_CONSUMER: FULL_THETA_H_NONNEGATIVITY
ACTUAL_CONSUMER_REQUIREMENT: nonnegative Fourier transform of mathscr_K_sigma for every required sigma and tau
ORIGINAL_REQUESTED_OBJECT: exact axis_strip_and_folded_increment_identities
ORIGINAL_OBJECT_IS: NOT_NECESSARY
ORIGINAL_OBJECT_NOTE: useful_exact_representation_not_a_necessary_interface_for_every_RH_route
KNOWN_WEAKER_INTERFACES:
  - direct full_H sign with vanishing signed errors
  - positive mixture of autocorrelations constructed independently of the target sign
FAILURE_TYPE: COUNTEREXAMPLE
FAILURE_TARGET: half_coefficient_only
EPISTEMIC_STATUS: RESEARCH_DEBT_FOR_GLOBAL_POSITIVITY
NOVELTY_AXIS: source_locked_normalization_and_explicit_folded_increment
REOPEN_TRIGGER: source_side_positive_factorization_or_full_signed_lower_envelope
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_REF: section_1_gaussian_negative_residual
ROUTE_FAMILY_KILLED: false
```

[ABSTRACT][PAPER] Директива Codex не отправлялась. Единственный следующий локальный вопрос при продолжении: дать исходную факторизацию полного нормированного ядра, сохраняющую смешанные члены, и проверить её точный дефект; не объявлять положительность Fourier-преобразования из положительности подынтегрального веса.

Запрещённый повтор: терять якобиан 1/2, удваивать самовклад нового горба, путать K с K_{sigma=0}, отождествлять сложенную конечную сумму с контурной головой без (5.3). Минимальная оставшаяся неизвестная — знак Fourier-преобразования полного mathscr K_sigma; его построение в этом раунде не заявлено.

Verification handoff: публикуется только этот новый markdown-документ; Lean-файлы и состояние маршрута не меняются. Commit SHA и Git blob публикации возвращаются в сообщении доставки. Kernel gate не запускался и к текстовому документу не приписывается. Требуется внешняя проверка аналитического доказательства; точные алгебраические контроли приложены отдельно локально.
