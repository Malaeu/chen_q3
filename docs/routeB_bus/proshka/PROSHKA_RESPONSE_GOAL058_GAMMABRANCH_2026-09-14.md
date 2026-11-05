# STATUS: KILL_GAMMA_COFINAL_REAL_ZERO_FAMILY
```yaml
OPERATIVE_CLASS: KILL_GAMMA_COFINAL_REAL_ZERO_FAMILY
REQUEST_ID: REQ-2026-09-14-GAMMABRANCH
BOUNDARY_ID: GOAL058_GAMMA_COFINAL_BRANCH_OBSTRUCTION_AUDIT
REQUEST_COMMIT: 15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1
REQUEST_BLOB: e5eb87dc284e554b3a1458a43a9d34eb2ebe9561
SOURCE_BASE: d838c57e3975eadab74ea85acfacbac570284451
AUDITED_REPORT_BLOB: 7c4026d4374f70ec87cc20c187007c89196d5e58
AUDITED_REPORT_SHA256: 862011bd19d73961d2270c8b7da61f63d30e68e2d195c4846497d9f1c2c39f63
AUDITED_REPORT_LOCAL_BYTES: 11413
AUDITED_REPORT_LOCAL_LF: 238
AUDITED_REPORT_BYTE_AND_BLOB_CHECK: MATCH
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
AUDIT_RESULT: ACCEPT_B1_B8_WITH_EXPLICIT_ANALYTIC_COMPLETIONS
STATEMENT_OR_SOURCE_CHANGED: false
KILL_SCOPE: ROUTE_FAMILY
KILL_FAMILY: EXACT_RECIPROCAL_FINITE_GAMMA_REAL_ZERO_APPROXIMANTS
KILL_EVIDENCE_KIND: ANALYTIC_INFINITELY_MANY_NONREAL_ZEROS_FOR_EVERY_N_GE_13
KILL_EVIDENCE_REF: Sections 3-10; source report B1-B8 at the pinned commit
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS_NAMED_FAMILY: MATHEMATICALLY_DEAD_AS_ALL_REAL_ZERO_SUPPLIER
EPISTEMIC_STATUS_ACTUAL_SOURCE_SIGN: RESEARCH_DEBT
THEOREM_QUANTIFIERS: every integer N>=13 and every fixed real h
THEOREM: normalized Fourier transform of exp(h*x^2)*G_N has infinitely many distinct nonreal zeros
ALL_REAL_ZERO_COFINAL_SUBSEQUENCE: EXCLUDED
ARBITRARY_FINITE_REAL_GAUSSIAN_PARAMETER_PER_MEMBER: ALSO_EXCLUDED
N2_THROUGH_N12_ZERO_LOCATION: NOT_DECIDED
N1_BESSEL_RESULT: PRESERVED_NOT_REPROVED
ORIGINAL_H0_LIMIT_TO_XI: PRESERVED
ACTUAL_THETA_NEGATIVE_WITNESS: NOT_SUPPLIED
GLOBAL_V_IC_ODD2_RH: OPEN_UNCHANGED
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INDEPENDENT_ANALYTIC_AUDIT_OF_CODEX_REPORT: PERFORMED
ADDITIONAL_REVIEWER_SPAWNED_BY_THIS_TURN: false
LEAN_VERIFIED: false
NUMERICAL_ZERO_SEARCHES: 0
DENSITY_OR_TRANSFORM_EVALUATIONS: 0
QUADRATURES: 0
GRIDS: 0
EXACT_RATIONAL_ARITHMETIC_ONLY: true
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
SOURCE_SIGN_COUNTERS: NOT_CHANGED_OR_RESET
CANONICAL_ADMISSION: false
PX_RH_CLAIM: NOT_MADE
PUBLICATION_BRANCH: codex_mac/gamma-reciprocity-20260914
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_GAMMABRANCH_2026-09-14.md
```

AUTOPSY: dropped=COUPLING; note=The geometric reciprocal square root preserves the real-axis source limit but creates uncancelled odd branch divisors inside the source strip. Their finite nearest-height contribution bounds the real transform-zero count by O(T), incompatible with imaginary-axis growth if only finitely many zeros were nonreal. No term is dropped in this audit; this is the failed preservation premise of the named approximation family, not a negative value of the actual theta form.

## 1. Решение и область

**B1–B8 выдерживают независимую аналитическую проверку.** Принимаю их заключение на **PAPER-уровне**: для каждого целого **N>=13** и каждого фиксированного **h in R** функция
\[
 M_{N,h}(z)=\frac{1}{Z_{N,h}}\int_{\mathbb R}
 e^{h x^2}\sqrt{r_N(e^{2x})r_N(e^{-2x})}\,e^{-izx}\,dx,
 \qquad Z_{N,h}>0,
\tag{1}
\]
имеет **бесконечно много различных невещественных нулей**. Кратности конечны, поскольку функция целая и равна 1 в нуле. `[COFINAL_FAMILY][PAPER]`

Это исключает **всю указанную кофинальную семью** как поставщика функций только с вещественными нулями. **Кофинальность** здесь означает неограниченную последовательность целых N. Любая такая последовательность достигает N>=13. Разрешение выбирать произвольное конечное вещественное h_N отдельно для каждого N не помогает. Речь уже не только о прежнем скалярном Sturm-lift. `[COFINAL_FAMILY][PAPER]`

Сходимость исходных M_{N,0} к нормированной xi сохраняется. Заключение **не** доказывает невещественный нуль предельной xi, отрицательную исходную V или ложность RH. Случаи N=2,...,12 остаются неразрешёнными этим аргументом. `[ABSTRACT][PAPER]`

Ниже развёрнуты наиболее сжатые места B4–B7: глобальная ветвь, все края разрезанного контура, равномерная ошибка в спектральной полосе и единые диски Jensen. Формулы и утверждение входного отчёта менять не требуется. Дополнения являются доказательствами условий, а не новыми гипотезами.

## 2. Источники, проверки и карта B1–B8

Протокол прочитан через GitHub в `rh_clean`, строки 1–220 и 221–конец, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. Управляющий запрос прочитан целиком по commit из YAML. Старые вложения не выбирали текущую задачу.

**[B]** [Полный проверяемый отчёт B1–B8](https://github.com/Malaeu/chen_q3/blob/15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1/docs/Codex/REPORT_2026-09-14_GAMMA_COFINAL_BRANCH_OBSTRUCTION.md) прочитан целиком. Полученные UTF-8 bytes сохранены локально: **11413 bytes, 238 LF, final LF, CR0**. Независимо пересчитаны и совпали SHA-256 из запроса и Git blob из YAML.

**[G]** [Полный исходный гамма-мост](https://github.com/Malaeu/chen_q3/blob/65c4a563ce4319a595a17e7c264dbbd77f1672e1/docs/Codex/REPORT_2026-09-14_GAMMA_RECIPROCITY_BRIDGE.md) прочитан целиком, G0–G7. GitHub подтвердил blob `12c3a22d9634093afc35ae2df5f2b93aaa7c0ec1`. Его закреплённый SHA-256 — `7c641d8a055bffc80fa2ed8d1ff437c1a47d6d0dfe3b82f9fa2533db02bda621`; в этой попытке этот SHA-256 отдельно не пересчитывался. Используются определения G1–G2, полный upper-tail G4 и fixed-N tails G6. Готовый предел не выдается за новое доказательство.

**[R]** [Управляющий запрос](https://github.com/Malaeu/chen_q3/blob/15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1/docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_GAMMABRANCH_2026-09-14.txt), blob `e5eb87dc284e554b3a1458a43a9d34eb2ebe9561`. В соседнем `GAMMA_RECIPROCITY_RECEIPTS_2026-09-14.json` прочитаны только строки 1–45, blob `20e6cd4318dc31a8faee7bcf7cddd0e0823d1387`. Полного чтения его вложенных журналов и повторного исполнения чужих reviews не заявляю. Слова CLEAN и прежние квитанции не используются вместо доказательства.

Внешние аналитические зависимости проверены непосредственно:

- **[W]** [NIST DLMF 2.4(i), (2.4.1)](https://dlmf.nist.gov/2.4#E1): комплексная форма Watson. Для нужного здесь конечного разреза ниже дан собственный остаточный бюджет, поэтому одной ссылки на Watson недостаточно и она не заменяет §7.
- **[C]** [NIST DLMF 1.10(iv), (vi)](https://dlmf.nist.gov/1.10): Rouché и аналитические ветви. Конкретное продолжение построено в §6.
- **[JH]** [T. Tao, 246B Notes 1, Theorems 2 и 22](https://terrytao.wordpress.com/2020/12/23/246b-notes-1-zeroes-poles-and-factorisation-of-meromorphic-functions/): Jensen и Hadamard для целых функций конечного порядка. Используется степень не выше 1 у экспоненциального полиномиального множителя; конечный экспоненциальный тип заранее не предполагается.

Это первичная авторская экспозиция стандартных теорем и официальные формулы, не новый импорт утверждения о нулях xi. Старый scalar-lift отчёт и рекурсивные архивы не перечитывались: новый барьер от них не зависит. `[ABSTRACT][PAPER]`

| Вход | Решение | Существенная проверка | Scope / verifier |
|---|---|---|---|
| B1 | ACCEPT | Двойные полюса, факториалы, точный порог N=13 | ABSTRACT / PAPER |
| B2 | ACCEPT | Обе строгие отрицательные рациональные огибающие | COFINAL_FAMILY / PAPER |
| B3 | ACCEPT | Rouché, простота, zero-free punctured disk при обращении | COFINAL_FAMILY / PAPER |
| B4 | ACCEPT WITH DETAILS BELOW | Минимальная высота достигается; глобальная ветвь на разрезах существует | ABSTRACT / PAPER |
| B5 | ACCEPT WITH DETAILS BELOW | Все контурные края; ненулевые скачки; fixed-band ошибка | ABSTRACT / PAPER |
| B6 | ACCEPT WITH DETAILS BELOW | Центр не вырождается; радиусы и upper bound едины по положению диска | ABSTRACT / PAPER |
| B7 | ACCEPT | Order <=1, парное произведение, O(T) против T log T | ABSTRACT / PAPER |
| B8 | ACCEPT | Любое фиксированное вещественное h; никаких uniform-in-h предпосылок | COFINAL_FAMILY / PAPER |

## 3. B1: независимая проверка коэффициентов

Зафиксируем произвольное целое N>=13. Положим lambda_n=pi*n^2. Плотность r_N — свёртка **всех** 2N экспоненциальных плотностей, по две с каждым rate. Поэтому она положительна при t>0. Её Laplace-transform равен
\[
 R_N(s)=\prod_{n=1}^N\frac{\lambda_n^2}{(s+\lambda_n)^2}.
\]
Коэффициент двойного полюса в s=-lambda_n:
\[
 d_n=\lambda_n^2\prod_{m\ne n}
 \frac{\lambda_m^2}{(\lambda_m-\lambda_n)^2}.
\tag{2}
\]
Для проверки факториалов отдельно вычислим
\[
 \prod_{m\ne n}(m^2-n^2)
 =(-1)^{n-1}\frac{(N-n)!(N+n)!}{2n^2},
 \qquad \prod_{m\ne n}m^2=\frac{(N!)^2}{n^2}.
\]
Отсюда **буквально**
\[
 d_n=\frac{4\pi^2n^4(N!)^4}{[(N-n)!(N+n)!]^2}>0.
\tag{3}
\]
Коэффициент простого полюса также конечен и вещественен:
\[
 e_n=-2d_n\sum_{m\ne n}\frac1{\lambda_m-\lambda_n}.
\]
Обратное преобразование каждого слагаемого даёт всю плотность
\[
 r_N(t)=\sum_{n=1}^N(d_nt+e_n)e^{-\pi n^2t}.
\tag{4}
\]
Это одновременно её целое продолжение по t. `[ABSTRACT][PAPER]`

Далее
\[
 \frac{d_2}{d_1}=16\left(\frac{N-1}{N+2}\right)^2
 \ge16\left(\frac{12}{15}\right)^2=\frac{256}{25},
\tag{5}
\]
поскольку (N-1)/(N+2) возрастает. Для 3<=n<=N:
\[
 \frac{d_n}{d_2}
 =\frac{n^4}{16}\prod_{j=2}^{n-1}
 \left(\frac{N-j}{N+j+1}\right)^2\le\frac{n^4}{16}.
\tag{6}
\]
Все множители положительны и не превосходят 1. При n>N коэффициентов нет; продолжение **мажоранты** суммой до бесконечности далее только увеличивает upper bound и не меняет источник. `[COFINAL_FAMILY][PAPER]`

## 4. B2: отрицательный корень и строгая простота

Пусть P_N(w)=sum_{n=1}^N d_n w^{n^2-1}, D_N(w)=wP_N(w). При w=-r, r>0, чётные n дают отрицательные члены, нечётные — положительные. При r=1/2 из (5)–(6):
\[
 \frac{P_N(-1/2)}{d_2}
 \le\frac{25}{256}-\frac18+\frac{81}{4096}
 +\sum_{n=5}^{\infty}\frac{n^4}{16}2^{-(n^2-1)}.
\tag{7}
\]
Отношение соседних членов последней суммы при n>=5 не больше
\[
 (6/5)^4 2^{-11}=81/80000<1/256.
\]
Первый член равен 625/2^28. Следовательно
\[
 \boxed{\frac{P_N(-1/2)}{d_2}
 \le-\frac{31}{4096}+\frac{256}{255}\frac{625}{2^{28}}
 =-\frac{404611}{53477376}<0.}
\tag{8}
\]
Вместе с P_N(0)=d_1>0 это даёт w_0=-r_0, 0<r_0<1/2. `[COFINAL_FAMILY][PAPER]`

Простота требует отдельного аргумента. Для каждого 0<r<=1/2:
\[
 \frac{\frac{d}{dr}P_N(-r)}{3d_2r^2}
 \le-1+\frac{27}{2}r^5
 +\sum_{n=5}^{\infty}\frac{(n^2-1)n^4}{48}r^{n^2-4}.
\tag{9}
\]
Максимум мажоранты достигается при r=1/2. Первый хвостовой член там равен 625/2^22. Отношение соседних членов не больше
\[
 \frac{35}{24}(6/5)^4 2^{-11}=189/128000<1/256.
\]
Здесь каждый из трёх факторов отношения убывает с n>=5. Поэтому
\[
 \boxed{\frac{\frac{d}{dr}P_N(-r)}{3d_2r^2}
 \le-1+\frac{27}{64}+\frac{256}{255}\frac{625}{2^{22}}
 =-\frac{482947}{835584}<0.}
\tag{10}
\]
Корень на (-1/2,0) единственный и простой. Простой корень D_N в w_0 следует из w_0!=0. Это аналитические знаковые бюджеты для всех N>=13, не вычисление положения корня. `[COFINAL_FAMILY][PAPER]`

## 5. B3: Rouché и отсутствие взаимного сокращения

Запишем E_N(w)=sum e_n w^{n^2}. Пусть
\[
 \sigma=-\log r_0/\pi>0,\qquad t_j=\sigma+i(2j+1),\quad j\to+\infty.
\]
При t=t_j+zeta имеем точное равенство
\[
 \frac{r_N(t_j+\zeta)}{t_j+\zeta}
 =d(\zeta)+\frac{E_N(w_0e^{-\pi\zeta})}{t_j+\zeta},
 \qquad d(\zeta)=D_N(w_0e^{-\pi\zeta}).
\tag{11}
\]
По (10), d(0)=0 и d'(0)=-pi*w_0*D_N'(w_0)!=0. Выберем малый фиксированный delta>0 так, чтобы d/zeta не обращалась в ноль на |zeta|<=delta. Тогда |d(zeta)|>=k|zeta| с k>0, а |E_N(w_0e^{-pi*zeta})|<=C на этом диске.

При достаточно большом j второе слагаемое на |zeta|=delta меньше первого. По Rouché [C] внутри находится **ровно один нуль, считая кратность**. Поэтому он простой. В самом нуле из (11):
\[
 |\zeta_j|\le \frac{2C}{k|t_j|}.
\tag{12}
\]
Получены простые нули t_j^*=t_j+O(1/j) исходной r_N, с Re(t_j^*)>0 и Im(t_j^*)>0 для больших j. Деление на t_j+zeta законно на всём диске.

Свёртка 2N экспонент при нуле, или её simplex integral, даёт
\[
 r_N(t)=c_Nt^{2N-1}(1+O(t)),\qquad
 c_N=\frac{\prod_{n=1}^N\lambda_n^2}{(2N-1)!}>0.
\tag{13}
\]
Это комплексный Taylor-факт для целой функции (4). Есть eta_N>0, где r_N не имеет нулей при 0<|t|<eta_N. Так как 1/t_j^*->0 и 1/t_j^*!=0,
\[
 r_N(1/t_j^*)\ne0\quad\text{для всех достаточно больших }j.
\tag{14}
\]
Не используется предположение о местоположении нулей Fourier-transform.

Положим zeta_j=(1/2)Log(t_j^*) с главным логарифмом. Тогда 0<Im(zeta_j)<pi/4. Для целой функции
\[
 F_N(\zeta)=r_N(e^{2\zeta})r_N(e^{-2\zeta})
\]
получаем
\[
 F_N'(\zeta_j)=2t_j^*r_N'(t_j^*)r_N(1/t_j^*)\ne0.
\tag{15}
\]
Следовательно квадратный корень имеет подлинное **полуцелое ветвление**. Сопряжение даёт такой же нуль снизу. Формула (14) — обязательная проверка: произвольный нуль одного множителя без неё не доказывал бы ветвление произведения. `[COFINAL_FAMILY][PAPER]`

## 6. B4: ближайший слой и глобальная положительная ветвь

### 6.1. Конечность и достигаемость

Фиксируем 0<b<pi/4. При zeta=u+iv, |v|<=b, u->+infinity, имеем Re(e^{2zeta})>=cos(2b)e^{2u}. Из **конечной точной** формулы (4) и (13) равномерно:
\[
 r_N(e^{2\zeta})=(d_1e^{2\zeta}+e_1)e^{-\pi e^{2\zeta}}(1+o(1)),
\]
\[
 r_N(e^{-2\zeta})=c_Ne^{-2(2N-1)\zeta}(1+o(1)).
\tag{16}
\]
В первом отношении высшие rates подавлены множителем не больше константы times exp[-3pi*cos(2b)e^{2u}]; линейный знаменатель отделён от нуля при больших u. Во втором используется Taylor-оценка O(e^{-2u}). Поэтому оба множителя не обращаются в ноль за достаточно большим u. Симметрия F_N(-zeta)=F_N(zeta) закрывает отрицательный конец.

Все нули в закрытой полосе |Im(zeta)|<=b находятся в компакте и их конечное число. F_N не тождественный нуль и строго положительна на вещественной оси. Выбрав b больше высоты одного нуля из (15), получаем непустое конечное множество нечётных нулей ближе этого b. Минимальная глубина a поэтому **положительна и достигается**. Все нижние нечётные нули этой глубины обозначим
\[
 \zeta_l=b_l-ia,\qquad l=1,\ldots,L.
\tag{17}
\]
Числа b_l различны. Это минимум среди **нечётных** кратностей; более близкие нули чётной кратности не требуют разреза. `[ABSTRACT][PAPER]`

### 6.2. Конструкция ветви, а не её предположение

Можно выбрать eps>0 и eta>0 так, что a+eps<pi/4, 0<eta<a, нижняя граница Im(zeta)=-(a+eps) не содержит нулей, а в полосе
\[
 S=\{-(a+\mathrm{eps})<\Im\zeta<\eta\}
\]
единственные нули нечётной кратности — (17). Все нули в S конечны. eps можно дополнительно уменьшить так, чтобы каждый короткий вертикальный разрез от zeta_l до нижней границы лежал в изолирующем диске этого нуля. Никакая новая знаковая гипотеза для этого не нужна.

Удалим из F_N **все** нулевые множители в S, с их полными кратностями. Полученный F_0 голоморфен и нигде не равен нулю в просто связной полосе S, поэтому имеет голоморфный логарифм L_0. Для чётного нуля порядка 2k вернём полиномиальный множитель (zeta-zeta_*)^k. Для нечётного порядка 2m_l+1 вернём (zeta-zeta_l)^{m_l+1/2} с разрезом вертикально вниз. Их произведение с exp(L_0/2) — глобальный голоморфный квадратный корень на S с указанными разрезами. Выбор одного общего знака при zeta=0 делает его равным **исходному положительному G_N на всей вещественной оси**. `[ABSTRACT][PAPER]`

На каждом чётном нуле этот корень продолжается голоморфно; там нет скрытого контура или полюса. На двух берегах нечётного разреза значения отличаются знаком. Построение не предполагает целости G_N по zeta.

Из (16), после взятия модуля квадратного корня, следует для всей замкнутой полосы интегрирования и её берегов
\[
 |G_N(u+iv)|\le C\exp(C|u|-c e^{2|u|}),\quad -(a+\mathrm{eps})\le v\le0,
\tag{18}
\]
с положительными конечными C,c, зависящими от N и полосы. На компактной части bound увеличивается до единой константы. Вблизи нечётного нуля корень стремится к нулю, а не к бесконечности. Модуль любой ветви равен |F_N|^{1/2}, поэтому bound не зависит от выбора берега.

## 7. B5: полный перенос контура и uniform-in-band остаток

Здесь **z — спектральная переменная**, zeta — источник. Нельзя смешивать их полосы. Пишем z=q+iv, q>0, |v|<=B, где B заранее фиксировано и конечно.

У нуля (17) порядка 2m_l+1 локально
\[
 G_N(\zeta)=c_l(\zeta-\zeta_l)^{\alpha_l}
 (1+O(\zeta-\zeta_l)),\quad \alpha_l=m_l+\tfrac12,\quad c_l\ne0.
\tag{19}
\]
Пусть нижняя глубина b=a+eps. Интегрирование по разрезанному прямоугольнику с вертикалями Re(zeta)=+/-R даёт после пределов
\[
 Z_N M_N(z)=H_b(z)+\sum_{l=1}^{L}e^{-iz\zeta_l}
 \int_0^{\mathrm{eps}}e^{-zt}J_l(t)\,dt.
\tag{20}
\]
Здесь H_b — интеграл по нижней горизонтали, разделённый в местах выхода разрезов; в каждом сегменте используется граничное значение той же ветви. J_l включает ориентированную разность обоих берегов и d(zeta)=-i dt. В частности
\[
 J_l(t)=k_lt^{\alpha_l}+O(t^{\alpha_l+1}),\qquad |k_l|=2|c_l|>0.
\tag{21}
\]
Точная фаза k_l зависит от согласованной ориентации, но её модуль и ненулевость не зависят от неё. Фактор 2 следует из exp(2pi*i*alpha_l)=-1. Частота b_l не объединяется с иной такой же частотой, поскольку их нет.

**Все границы в (20) оплачены.** Вертикальные стороны имеют модуль не больше константы times exp((B+C)R-c e^{2R}) и исчезают. Малые окружности вокруг верхних концов разрезов дают O(delta^{alpha_l+1}) и исчезают при delta->0. У нижних концов ветви ограничены, поэтому соединительные дуги дают O(delta). Чётные нули не требуют обхода. Нижняя горизонталь абсолютно интегрируема, причём
\[
 |H_b(z)|\le e^{-bq}
 \int_{\mathbb R}|G_N(u-ib)|e^{B|u|}\,du
 \le C_Be^{-bq}.
\tag{22}
\]
Значения в конечном числе мест разрезов на горизонтали не влияют на интеграл. В (20) сначала берутся контурные пределы для фиксированного z, затем следующие оценки дают нужную равномерность.

Проверка знака затухания точна:
\[
 e^{-iz(\zeta_l-it)}=e^{-iz\zeta_l}e^{-zt},\qquad
 e^{-iz\zeta_l}=e^{-az}e^{-ib_lz}.
\tag{23}
\]
Никакого растущего exp(+zt) на нижних разрезах нет.

Для полной оплаты Watson достаточно элементарной оценки. При фиксированном alpha_l>-1 пусть
\[
 |J_l(t)-k_lt^{\alpha_l}|\le K_l t^{\alpha_l+1}
 \quad(0<t\le\mathrm{eps}).
\]
Тогда, используя Laplace-integral Gamma при Re(z)>0,
\[
 \begin{split}
 \left|\int_0^{\mathrm{eps}}e^{-zt}J_l(t)dt
   -k_l\Gamma(\alpha_l+1)z^{-\alpha_l-1}\right|
 \le{}&K_l\Gamma(\alpha_l+2)q^{-\alpha_l-2}\\
 &+|k_l|\Gamma(\alpha_l+1)(2/q)^{\alpha_l+1}
 e^{-q\mathrm{eps}/2}.
 \end{split}
\tag{24}
\]
Первое слагаемое — абсолютный интеграл Taylor-остатка. Второе оплачивает хвост от eps до бесконечности в Gamma-integral; используется e^{-qt}<=e^{-q eps/2}e^{-qt/2}. Комплексная степень z берётся в правой полуплоскости. Нет незаконной замены вещественного пути t на комплексный u/z.

Положим alpha=min_l alpha_l и p=alpha+1. Из (20)–(24), |e^{-ib_lz}|<=e^{B|b_l|} и |z|/q bounded при q>=1 получаем
\[
 \boxed{U(z):=e^{az}z^pM_N(z)=P(z)+O_{N,B}(q^{-1}),}
\]
\[
 P(z)=\sum_{\alpha_l=\alpha}C_le^{-ib_lz},\qquad
 C_l=\frac{k_l\Gamma(\alpha+1)}{Z_N}\ne0,
 \quad q\to+\infty,\ |\Im z|\le B.
\tag{25}
\]
Высшие alpha_l-alpha — положительные целые числа, поэтому их вклад не больше O(q^{-1}). Нижняя горизонталь после нормировки ограничена C_B|z|^p exp(-eps*q), также O(q^{-1}). Невырожденность P подтверждается следующим L2-расчётом, а не предполагается. `[ABSTRACT][PAPER]`

## 8. B6: невырожденный центр и единые диски Jensen

Суммируем в P только частоты из (25). Обозначим
\[
 S_0=\sum_l|C_l|^2>0,\qquad
 D_0=\sum_{l\ne j}\frac{2|C_lC_j|}{|b_l-b_j|}<\infty.
\]
Для любого A и L>0 прямое интегрирование экспонент даёт
\[
 \int_A^{A+L}|P(s)|^2ds\ge LS_0-D_0.
\tag{26}
\]
Выберем L_*=1+2D_0/S_0 и c_*=sqrt(S_0/2). На каждом [A,A+L_*] имеется s=s_A с |P(s)|>=c_*. В частности P не тождественный нуль, даже если его значения в отдельных точках равны нулю.

При всех достаточно больших A ошибка в (25) на вещественной оси меньше c_*/2. Поэтому
\[
 |U(s_A)|\ge c_*/2>0.
\tag{27}
\]
Теперь **один раз** фиксируем r_*=L_*+2 и спектральную ширину B=2r_*. Для большого A весь закрытый диск |z-s_A|<=2r_* лежит в Re(z)>0 и в области равномерной (25). На нём
\[
 |U(z)|\le H_*:=1+\sum_l|C_l|e^{2r_*|b_l|},
\tag{28}
\]
после дополнительного увеличения нижнего порога A. Константы r_*, H_*, c_* не зависят от A. По Jensen [JH, Theorem 2]:
\[
 n_U(s_A,r_*)\log2
 \le\log\frac{H_*}{|U(s_A)|}
 \le\log\frac{2H_*}{c_*}.
\tag{29}
\]
Если нуль попал на внешнюю окружность, используем радиусы, возрастающие к 2r_* и не содержащие нулей; та же оценка следует пределом. Для включения внутренней окружности можно аналогично взять внутренний радиус чуть больше r_* и перейти обратно. Все нули считаются с кратностью.

Диск меньшего радиуса включает [A,A+1], потому что s_A in [A,A+L_*]. Значит каждое достаточно далёкое единичное вещественное звено содержит равномерно ограниченное число нулей U. Множители exp(az) и z^p не имеют нулей в правой полуплоскости, поэтому это те же нули M_N. Начальный компакт содержит конечное число нулей. Чётность даёт
\[
 \boxed{n_{\mathbb R,N}(T)=O_N(T).}
\tag{30}
\]
Это доказано независимо от предположения о числе невещественных нулей. Одна асимптотика лишь на вещественной оси не оплатила бы (28); здесь используется именно полная fixed-band оценка (25). `[ABSTRACT][PAPER]`

## 9. B7: порядок, рост и парная факторизация

### 9.1. Две независимые оценки роста

Из полного G4 в [G]
\[
 G_N(x)\le C\exp[-(\pi/2)\cosh(2x)]
 \le C\exp[-(\pi/4)e^{2|x|}].
\tag{31}
\]
Для |z|<=R модуль Fourier-integral ограничен integral e^{R|x|}G_N(x)dx. Вынеся максимум Rx-(c/2)e^{2x} на x>=0 и сохранив интегрируемый фактор exp[-(c/2)e^{2x}], получаем
\[
 \log\max_{|z|\le R}|M_N(z)|=O_N(R\log(R+2)).
\tag{32}
\]
Это даёт **порядок не выше 1**, но НЕ конечный экспоненциальный тип. Доминирование (31) с любым e^{R|x|}|x|^k также доказывает целость M_N и допустимость всех фиксированных z-производных.

Обратно, (4) при t->+infinity и (13) при t->0 дают
\[
 G_N(x)\sim\sqrt{d_1c_N}\,
 e^{-2(N-1)x}\exp[-(\pi/2)e^{2x}],\qquad x\to+\infty.
\tag{33}
\]
В частности существуют фиксированные положительные c,A,B и x_0, где G_N(x)>=c exp[-A e^{2x}-B x] при x>=x_0. На [0.5 log T,0.5 log T+1] при большом T всё подынтегральное выражение в M_N(iT) положительно. Длина интервала равна 1. Поэтому
\[
 \boxed{\log M_N(iT)\ge\tfrac T2\log T-C_1T-C_2\log T-C_3.}
\tag{34}
\]
Вся исходная плотность сохранена: asymptotic (33) используется лишь для выведенной односторонней оценки на хвосте, а не подставляется вместо полного Fourier-integral. `[ABSTRACT][PAPER]`

### 9.2. Почему конечное число невещественных нулей невозможно

Предположим противное: невещественных нулей конечное число. Hadamard [JH, Theorem 22] при порядке <=1 даёт произведение факторов E_1(w)=(1-w)e^w и экспоненту exp(Az+B). Нуля при z=0 нет, поскольку M_N(0)=1.

Чётность обеспечивает равные кратности нулей zeta и -zeta. Группировка законна: genus-one произведение локально нормально сходится; для вещественных нулей отдельно из (30) следует sum rho_j^{-2}<infinity. В паре
\[
 E_1(z/\zeta)E_1(-z/\zeta)=1-z^2/\zeta^2.
\]
Все конечные невещественные пары уходят в чётный полином Q_0. Получаем
\[
 M_N(z)=e^{Az+B}Q_0(z)\prod_{\rho_j>0}(1-z^2/\rho_j^2).
\]
Отношение при z и -z на окрестности нуля даёт exp(2Az)=1 тождественно, значит A=0. Константу exp(B) включаем в Q_0. Следовательно
\[
 M_N(z)=Q_0(z)\prod_{\rho_j>0}(1-z^2/\rho_j^2).
\tag{35}
\]
Это не предположение принадлежности Laguerre–Pólya и не использование RH.

При наличии положительных вещественных нулей их минимальное значение rho_*>0. Из (30) есть K>0 с n_+(t)<=Kt для всех t>=rho_*, а ниже rho_* счёт равен нулю. Интегрирование Стилтьеса, с нулевыми граничными членами, даёт
\[
 \begin{split}
 \sum_j\log(1+T^2/\rho_j^2)
 &=2T^2\int_0^\infty\frac{n_+(t)}{t(t^2+T^2)}dt\\
 &\le 2KT^2\int_0^\infty\frac{dt}{t^2+T^2}=\pi KT.
 \end{split}
\tag{36}
\]
При отсутствии положительных нулей левая часть нулевая. На бесконечности граничный член исчезает как O(T^2/t), у нуля исчезает потому, что n_+(t)=0. Фиксированный полином в (35) добавляет не больше O(log(T+2)). Поэтому из (35) следовало бы
\[
 \log|M_N(iT)|\le\pi KT+C_4\log(T+2)+C_5.
\tag{37}
\]
Это противоречит (34). Разность upper bound (37) и lower bound (34) для всех достаточно больших T не больше
\[
 -\tfrac14T\log T<0.
\tag{38}
\]
Получена строгая несовместимость огибающих, а не просто неудача достаточного условия. Следовательно **невещественных нулей бесконечно много**. `[ABSTRACT][PAPER]`

## 10. B8: любой фиксированный Gaussian-множитель

Пусть h — произвольное фиксированное вещественное число и K_{N,h}(zeta)=exp(h*zeta^2)G_N(zeta). Его квадрат exp(2h*zeta^2)F_N(zeta) имеет ровно те же нули с теми же кратностями. Нечётные разрезы (17) остаются ближайшими; каждый c_l и k_l умножается на exp(h*zeta_l^2)!=0.

В source-strip
\[
 |e^{h(u+iv)^2}|\le e^{|h|u^2+|h|b^2}.
\]
Этот множитель поглощается двойным экспоненциальным спадом (18). Все контурные края §7 снова исчезают. Аналитический локальный множитель меняет только k_l,K_l в (21),(24). Поэтому
\[
 e^{az}z^p M_{N,h}(z)=P_h(z)+O_{N,h,B}(1/\Re z)
\tag{39}
\]
равномерно в каждой фиксированной спектральной полосе. Частоты те же; **каждый** ведущий коэффициент ненулевой. Лемма (26) и Jensen применяются с константами, зависящими от N,h. Получаем n_{R,N,h}(T)=O_{N,h}(T).

Для maximum-modulus bound используем конечную константу C_h такую, что
\[
 |h|x^2\le(\pi/8)e^{2|x|}+C_h\quad(x\in\mathbb R).
\]
Из (31) следует K_{N,h}(x)<=C'_h exp[-(pi/8)e^{2|x|}]. Нормировка Z_{N,h} конечна и положительна. Поэтому весь transform остаётся целым порядка <=1.

Для нижней оценки на прежнем интервале можно всегда использовать
\[
 e^{h x^2}\ge e^{-|h|(\tfrac12\log T+1)^2}.
\]
Так что (34) теряет не более O_h((log T)^2). Это o(T), и противоречие с (37) остаётся. Итак,
\[
 \boxed{\forall N\ge13\ \forall h\in\mathbb R:
 \#\{z\notin\mathbb R:M_{N,h}(z)=0\}=\infty.}
\tag{40}
\]
Равномерность констант по N или h **не требуется**. В частности произвольный выбор конечных h_N, даже неограниченных с N, не даёт ни одного all-real-zero члена при N>=13. Предел при h_N, зависящем от N, здесь не утверждается. `[COFINAL_FAMILY][PAPER]`

## 11. Adversarial checks и точная граница отказа

**Чётная кратность вместо ветвления.** Квадрат (zeta-zeta_0)^2 имеет голоморфный корень и нулевой скачок; такого аргумента было бы недостаточно. В §5 кратность произведения ровно 1, а §6 выбирает слой нечётных кратностей. Условие не пропущено.

**Взаимное сокращение.** Нуль r_N(t_*) мог бы совпасть с нулём r_N(1/t_*), сделав порядок чётным. (13)–(15) прямо исключают это для построенной последовательности, без догадки о всех нулях r_N.

**Отдельные особые точки против целого контура.** Минимальная высота не берётся как недостижимый infimum. Конечность в каждом меньшем закрытом strip даёт достигнутый a и положительный зазор eps. В §6 построена одна глобальная ветвь, а в §7 оплачены и верхние, и нижние концы разрезов.

**Почти сокращающиеся экспоненты.** Не требуется lower bound |P(t)| на всей прямой. (26) даёт один невырожденный центр в каждом длинном интервале. Если бы частоты совпадали, противоположные коэффициенты могли бы сократиться; различие b_l является обязательной проверкой. Единая ширина band фиксируется до Jensen.

**Порядок 1 против экспоненциального типа.** Из (32) не следует O(T) роста на мнимой оси. Именно дополнительное предположение о конечном числе невещественных нулей вместе с (30) и Hadamard создаёт (37). Ни одна из этих трёх частей не заменяется другой.

**Изолированное N против cofinal.** Оценки (8),(10) доказаны для произвольного N>=13. Остальной аргумент фиксирует это N и не требует одинаковых констант для различных N. Поэтому (40) запрещает любую неограниченную подпоследовательность этой семьи, а не только N=13.

**Нули приближения против нулей предела.** Доказанная локально равномерная сходимость M_{N,0}->xi(1/2-iz)/xi(1/2) не превращает подвижные невещественные нули в нуль xi вне оси. В этой работе нет общего компактного диска вне оси с сохранённым нулём при N->infinity. Координаты невещественных нулей M_{N,h} не вычислены. `[ABSTRACT][PAPER]`

**DISCRIMINATOR:** в текущем KILL нет zero-consistent численной неопределённости. Решающее различие — (30) против (34) через (35), со строгим разрывом (38). Для возможного утверждения о предельной xi понадобился бы отдельный фиксированный zero-free-boundary диск вне R и оплаченный Rouché margin при N->infinity; такого утверждения и такого диска здесь нет. `[ABSTRACT][CONDITIONAL]`

## 12. Consumer-first contract и закрытие аудита

| Поле | Точная запись |
|---|---|
| DOWNSTREAM_CONSUMER | Исходный полный знак V / опубликованный Weil criterion; в данной вспомогательной ветке — Hurwitz real-zero approximation criterion |
| ACTUAL_CONSUMER_REQUIREMENT | Та же нормированная последовательность должна одновременно сходиться к xi и не иметь невещественных нулей |
| NAMED_CANDIDATE_X | Неограниченная последовательность M_{N_j,0} только с вещественными нулями |
| ORIGINAL_OBJECT_IS | UNKNOWN как необходимое условие RH; используется только как достаточный интерфейс |
| KNOWN_WEAKER_INTERFACES_WITHIN_TESTED_CLASS | Любая cofinal подпоследовательность; произвольное конечное вещественное h_N на каждом члене. Обе исключены (40) |
| FAILURE_TYPE | INCOMPATIBILITY: член при N>=13 имеет бесконечно много невещественных нулей |
| EPISTEMIC_STATUS | MATHEMATICALLY_DEAD только для указанной семьи как all-real-zero supplier; общий источник — RESEARCH_DEBT |
| KILL_SCOPE | ROUTE_FAMILY, не весь RH Route B и не все гамма/Brownian конструкции |
| IMPOSSIBILITY_EVIDENCE | (8)–(15), (18)–(30), (32)–(40); B1–B8 в [B] |
| NOVELTY_AXIS | Независимое подтверждение барьера для всей cofinal семьи и fixed-Gaussian расширения, не повтор scalar-lift отказа; библиографическая новизна не заявляется |
| REOPEN_TRIGGER_NAMED_FAMILY | Конкретная ошибка одного из доказанных переходов (2)–(40), а не иной способ доказать ложное all-real утверждение |
| REOPEN_TRIGGER_ACTUAL_SOURCE_SIGN | Новый source-derived аргумент о самом V либо иной точно идентифицированный потребитель; этот аудит его не конструирует |

Все строки этой таблицы имеют scope **ABSTRACT** и verifier **PAPER**; строка о новых неустановленных поставщиках имеет verifier **CONDITIONAL**.

**ROUTE MAP.** B1–B3 дают реальное ветвление; B4–B5 дают ненулевую конечную экспоненциальную сумму; B6 даёт O(T) real-zero count; B7–B8 дают scoped KILL. Полный источник и предельный мост остаются корректными данными, но эта семья больше не может оплачивать их real-zero предпосылку. Для N=2,...,12 никакого решения не принято.

Два представления **того же проверяемого барьера**, не новые модели или задания: source-side разрезанный контур с (24) — kill-power 10/10, аналитическая стоимость 5/10; spectral-side Jensen/Hadamard с (36) — kill-power 10/10, стоимость 3/10. Оба использованы в аудите. Оценки качественные, не сроки и не основания истинности.

**FINAL PROPOSAL:** принять `ACCEPT_GAMMA_BRANCH_OBSTRUCTION_ALL_N_GE13_AND_FIXED_GAUSSIAN_ONLY`. Не заказывать новый пресервер неизменённой заведомо исключённой cofinal семьи. Не переносить KILL на предельную xi, V, IC, ODD2 или другие семейства.

Регистрация перед новыми независимыми проверками сохранена в Appendix A. Она сделана после первого чтения источника, не до любого размышления, и не является независимо заверенной timestamp-квитанцией. Судьба ставок:

| Prediction | Исход |
|---|---|
| P1: коэффициенты и две рациональные границы | CONFIRMED, §§3–4 и Appendix B |
| P2: ветвление без reciprocal cancellation | CONFIRMED, §5 |
| P3: глобальный contour и fixed-band completion | CONFIRMED, §§6–7; дополнения не меняют утверждение |
| P4: Jensen/Hadamard contradiction | CONFIRMED, §§8–9 |
| P5: все фиксированные Gaussian-множители | CONFIRMED, §10 |

**Что уменьшилось:** устранена возможность использовать какую-либо cofinal подпоследовательность этой конкретной семьи как all-real-zero приближение, включая указанное Gaussian-расширение. **Что не уменьшилось:** неоплаченная положительность полной исходной формы. **Что нельзя повторять:** заявлять cofinal real-zero-preserver для той же G_N или считать прежний scalar KILL пределом нового вывода. **Минимальный неоплаченный переход внутри B1–B8:** отсутствует после явно выписанных деталей. Самостоятельная задача о V этим не решена.

Memory entry: конечная reciprocal gamma-семья сходится к правильному источнику, но её квадратный корень имеет ближайший конечный слой нечётных комплексных дивизоров; real-zero counting становится O(T), а рост сохраняет T log T. Same-family convergence и real-zero property нельзя оплачивать разными объектами.

Это независимый аудит одного готового доказательства, не новый source-sign опыт. Исторические счётчики, runtime, очереди и canonical writer не меняются. Route score: 4 за проверенное исключение всей точной вспомогательной семьи, не оценка близости RH.

## 13. Одна директива и техническая передача

**CODEX DIRECTIVE:** принять только завершённый аудит B1–B8 в указанной области. При финальном intake сверить source SHA/blob, формулы (8),(10), построение глобальной ветви §6, cut budgets (20)–(24), fixed-band Jensen disks (26)–(29), парную факторизацию (35) и fixed-h аргумент §10. Единственный допустимый отказ — назвать конкретное неверное равенство или неоплаченное условие. Отсутствие RH-доказательства не опровергает этот scoped результат. Gate success: `ACCEPT_GAMMA_BRANCH_OBSTRUCTION_ALL_N_GE13_AND_FIXED_GAUSSIAN_ONLY`; failure: `GAMMABRANCH_FIRST_INVALID_STEP_<section_equation>`.

Отчёт сначала сохранён локально. Разрешена ровно одна новая remote-запись по пути YAML в ветке `codex_mac/gamma-reciprocity-20260914`, с префиксом `[Proshka]` у commit message. Старые файлы не перезаписываются. Resulting commit SHA возвращается отдельно после реальной операции записи; собственный будущий commit hash в содержимое не выдумывается. После записи проверяются новый blob и список изменённых путей.

**WORKDIR:** любой локальный каталог; сохранить Appendix B как `check_rationals.py`, затем `python check_rationals.py`. Все данные скрипта фиксированы. Для иной папки используется `python {folder}/check_rationals.py`, например `python /tmp/gammabranch/check_rationals.py`; подстановка меняет только путь, не математику. Это проверяет рациональные константы, а не контурные доказательства.

Lean-файлов нет; Lean gate, axiom profile и kernel verification — **NOT_RUN / NOT_APPLICABLE**. Git commit сам по себе не превращает текст в Lean theorem. Этот аудит является PAPER-проверкой независимого Codex-аргумента; ещё один отдельный проверяющий в этой сессии не запускался. Возможный intake повышает лишь статус scoped PAPER-результата, не статус RH.

## Appendix A. Буквальная регистрация

```text
REQ-2026-09-14-GAMMABRANCH — registration before the independent analytic tests
Source request: 15fe3eb8ee19c85c51f3ad2984583dc95a0af2a1
Source report read; no numerical source evaluations or zero searches authorized.
P1 (0.85): the stated factorial ratios and the two rational margins are correct
uniformly for all integers N>=13; verification by exact algebra only.
P2 (0.80): simple right-half-plane density zeros yield genuine reciprocal
square-root branch points; a punctured zero-free disk excludes cancellation.
P3 (0.70): the nearest-branch contour argument is repairable into a uniform
fixed-spectral-band expansion; global continuation and cut endpoints are the
most likely places needing supplementary proof, not assumed from the word Watson.
P4 (0.85 conditional on P3): uniform Jensen disks and the paired Hadamard
factorization force infinitely many nonreal transform zeros for each N>=13.
P5 (0.80 conditional on P1-P4): every fixed real Gaussian multiplier preserves
this obstruction, with constants depending on both N and h.
No claim about N=2,...,12 or the nonreal zeros of limiting xi is registered.
This file is a producer registration, not an independent timestamp receipt.
```

## Appendix B. Исполненная точная арифметика

```python
"""Exact arithmetic checks for B2 only. No density/transform evaluations."""
from fractions import Fraction as Q

ratio_B3 = Q(6, 5)**4 / 2**11
ratio_B4 = Q(35, 24) * ratio_B3
margin_B3 = Q(31, 4096) - Q(256, 255) * Q(625, 2**28)
margin_B4 = 1 - Q(27, 64) - Q(256, 255) * Q(625, 2**22)
assert ratio_B3 == Q(81, 80000) < Q(1, 256)
assert ratio_B4 == Q(189, 128000) < Q(1, 256)
assert 16 * Q(12, 15)**2 == Q(256, 25)
assert margin_B3 == Q(404611, 53477376) > 0
assert margin_B4 == Q(482947, 835584) > 0
print('N13_COEFFICIENT_RATIO=256/25')
print('B3_TAIL_RATIO=81/80000 < 1/256')
print('B4_TAIL_RATIO=189/128000 < 1/256')
print('B3_NEGATIVE_UPPER_MARGIN=404611/53477376')
print('B4_NEGATIVE_UPPER_MARGIN=482947/835584')
print('SOURCE_EVALUATIONS=0; ZERO_SEARCHES=0; QUADRATURES=0; GRIDS=0; LEAN=0')
```

Буквальный stdout; exit 0, stderr пуст:

```text
N13_COEFFICIENT_RATIO=256/25
B3_TAIL_RATIO=81/80000 < 1/256
B4_TAIL_RATIO=189/128000 < 1/256
B3_NEGATIVE_UPPER_MARGIN=404611/53477376
B4_NEGATIVE_UPPER_MARGIN=482947/835584
SOURCE_EVALUATIONS=0; ZERO_SEARCHES=0; QUADRATURES=0; GRIDS=0; LEAN=0
```

Обе бесконечные мажоранты доказаны аналитически в §4; программа не заменяет их конечным диапазоном n. Ни r_N, ни G_N, ни M_N здесь не вычисляются. Конец полного аудита.
