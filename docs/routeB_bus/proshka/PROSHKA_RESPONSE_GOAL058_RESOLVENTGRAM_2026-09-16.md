# STATUS: KILL_RESOLVENTGRAM_NORMALIZED_MELLIN_CAUCHY_PULLBACK
```yaml
OPERATIVE_CLASS: KILL_RESOLVENTGRAM_NORMALIZED_MELLIN_CAUCHY_PULLBACK
REQUEST_ID: REQ-2026-09-16-RESOLVENTGRAM
BOUNDARY_ID: GOAL058_FULL_SOURCE_RESOLVENT_GRAM_TO_WEIL_KERNEL
REQUEST_COMMIT: 5fb0c0693427a870409446cf24416790f06e69f2
REQUEST_BLOB: 53214dd2ee4cf0ff5f5f0044c54886fb76da584d
REQUEST_SHA256: f8014d60f15d8ab17d8ae2bc7a2fa4e25d680e94d20988fb5ce7d8a2867ef514
REQUEST_BYTES: 79287
REQUEST_LF: 1597
REQUEST_CR: 0
REQUEST_FINAL_LF: true
ATTACHMENT_SHA256_AND_GIT_BLOB_LOCALLY_VERIFIED: true
SOURCE_BASE: b02b477c3b5af44af6ac7259bac8d4aa9fd6d369
CONTEXT_SHA256: 2b221e8a9dc9dc948a8e46d8f16b95e2d945b34071e8fa3eca5d221b4b43d01e
CONTEXT_BYTES: 69411
CONTEXT_SHA256_LOCALLY_VERIFIED: true
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
HONESTY_STATE: CHALLENGER_NOT_RH
KILL_SCOPE: THEOREM_SHAPE
TESTED_MAP: L_weighted_normalized_Mellin_congruence_of_G_src_tensor_exact_h2_Cauchy_kernel
KILLED_STATEMENT: K2_equals_eta_times_tested_Gram_plus_PSD_correction_for_any_fixed_eta_gt_0
KILL_EVIDENCE_KIND: strict_negative_spatial_defect_upper_envelope_and_exact_Fourier_finite_row_transfer
KILL_EVIDENCE_REF: RG19_RG20_RG23_RG24
TESTED_GRAM_PSD: true
TESTED_GRAM_DOMAIN: every_finite_complex_family_of_real_frequency_nodes
EXACT_SPATIAL_IMAGE: reflected_full_source_exponential_resolvent_filters_RG12_RG16
SIGNED_CORRECTION: explicitly_retained_RG10_and_RG17
NONNEGATIVE_BOUNDARY_REPAIR_FOR_THIS_MAP: impossible_even_for_arbitrary_PSD_additional_kernel
ANY_OTHER_SOURCE_TO_CONSUMER_MAP_KILLED: false
JOINT_TN_INFINITY_AND_RECIPROCITY_REFUTED: false
ORIGINAL_V_NEGATIVE_WITNESS: NONE
ORIGINAL_K2_NEGATIVE_WITNESS: NONE
FULL_V_SIGN: OPEN_UNCHANGED
RH_PROVED_OR_REFUTED: false
SCOPE: ABSTRACT
VERIFIER: PAPER
PROOF_STATE: PAPER_CANDIDATE_PENDING_INDEPENDENT_REVIEW
FAILURE_TYPE: COUNTEREXAMPLE_TO_NAMED_EXACT_TRANSFER_AND_POSITIVE_CORRECTION
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AT_NAMED_MAP_ONLY_PENDING_REVIEW
WIDER_RESOLVENT_ROUTE_STATUS: RESEARCH_DEBT
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
REGISTRATION_SHA256: 907ff3de29b62fae4f321524381432c3214adcfd1c0d95dfeafe3357cddbf53d
SOURCE_NUMERICAL_EVALUATIONS: 0
QUADRATURES: 0
ZERO_SEARCHES: 0
RANK_SWEEPS: 0
LEAN_RUNS: 0
INDEPENDENT_REVIEWER_SPAWNED: false
CANONICAL_ADMISSION: false
SOURCE_SIGN_COUNTERS: NOT_CHANGED_OR_RESET
PX_RH_CLAIM: NOT_MADE
PUBLICATION_BRANCH: codex_mac/gamma-reciprocity-20260914
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_RESOLVENTGRAM_2026-09-16.md
```

## 1. Итог и точная область

Ы. Проверен один явно построенный перенос: **нормированная Mellin-конгруэнция** исходного резольвентного Gram-ядра, умноженная на точное Cauchy-ядро потребителя. Конгруэнция означает применение одной линейной карты к обеим сторонам ядра с комплексным сопряжением первой стороны. Она действительно сохраняет положительность и конечна на каждой допустимой строке.

Но её результат **не равен** исходному \(K_2\). Более сильно, для построенного ниже \(\mathcal G\)
\[
\boxed{\forall\eta>0\quad\exists N<\infty,\ u_1,\ldots,u_N\in\mathbb R,
\ a\in\mathbb C^N:\quad
\sum_{i,j}\overline{a_i}\,[K_2(u_i,u_j)-\eta\mathcal G(u_i,u_j)]a_j<0.}
\tag{RG1}
\]
Следовательно нельзя получить \(K_2=\eta\mathcal G+\mathcal B\) с независимо неотрицательной граничной формой \(\mathcal B\). Исключение действует даже при разрешении **любого** дополнительного PSD-ядра, не только формы конечного ранга на границе. Все утверждения этого абзаца: `[ABSTRACT][PAPER]`.

Это отказ **данной карты и её постоянной положительной перенормировки**, а не всех интегральных карт из пространства S1. Параметр \(\eta\) проверяет возможность исправить коэффициент выбранного переноса; он не вводит требование строгой коэрцитивности в задачу о V.

Причина видна на полном физическом интеграле. Взаимность исходной theta даёт сокращение диагонали V при общем уходе узла к минус бесконечности. Положительный образ выбранной карты сохраняет ненулевую полную энергию. Эти два объекта нельзя связать положительной добавкой. Никакой член theta не отбрасывается; отрицателен **дефект переноса**, не V.

## 2. Прочитанные входы и регистрация

Весь авторитетный TXT, включая восемь полных записей внутри `BEGIN_PINNED_CONTEXT`, прочитан. Локально проверены его байты, LF, CR, SHA256 и Git blob; последний совпадает с GitHub в request commit. Контекст извлечён между маркерами без изменений и независимо совпал с объявленным SHA256. Это не только проверка короткого delivery binder.

| Обозначение | Полный встроенный источник | Использованная область |
|---|---|---|
| R | Управляющие §§1–6 текущего TXT | S1, S2, определения, область одной попытки |
| T | `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` | Mellin/Fourier-нормировки; §§3–8 и приём; точный конечный потребитель |
| TN | `docs/Codex/REPORT_2026-09-12_THETA_TN_INFINITY_INTAKE.md` | Принятый TN-infinity; отличия от Hermitian PSD и старые исключения |
| RP | `docs/Codex/REPORT_2026-09-14_EXACT_RECIPROCAL_PAIRING.md` | Комплексная взаимность; разграничение совместной и изолированной предпосылок |
| Y | `docs/Codex/REPORT_2026-09-15_JOINTSOURCE_Y_INTAKE.md` | Область прежнего LP-отказа; не новый тест |
| TT | `docs/Codex/REPORT_2026-09-16_CRITICAL_TILT_TN4.md` | Запрет сохранять аддитивные minors через степенной наклон |
| VD | `docs/Codex/REPORT_2026-09-16_VANDANTZIG_DUAL_FILTER.md` | Различие исходной и центральной Stieltjes-функций |
| VH | `docs/Codex/REPORT_2026-09-16_VANDANTZIG_HUNT_INTAKE.md` | Принятые ошибки публикаций; не используются как новые импорты |
| CR | `docs/Codex/REPORT_2026-09-16_CONVOLUTION_RECIPROCITY_RIGIDITY.md` | Взаимность не переносится на другие полные integer shapes |

Идентификацией всех встроенных байтов служит проверенный context hash. Рекурсивные архивы этих записей не перечитывались. Bootstrap получен через GitHub из `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`.

Новая внешняя проверка ограничена первичными формулами NIST DLMF: **4.36.1** — полный sinh product; **5.2.1–5.2.2** — Gamma-интеграл, отсутствие нулей Gamma и определение digamma; **25.2.11** — Euler product при Re s>1. Адреса: `https://dlmf.nist.gov/4.36`, `https://dlmf.nist.gov/5.2`, `https://dlmf.nist.gov/25.2`. Никакая статья, заявляющая RH, и никакой новый GGC-preserver не импортируются. Теорема Вейля остаётся принятой зависимостью T; её историческое доказательство здесь не реконструируется.

После чтения и предварительного выбора карты, **до детальной проверки её доказательства**, локально записаны следующие предсказания. Предварительный вывод и выбор идеи не объявляются выполненными после регистрации.

| ID | p | Зарегистрированный проверяемый исход |
|---|---:|---|
| P_RG1 | 0.95 | Взвешенная Mellin/Cauchy-карта конечна и имеет точный обратный Fourier-образ через отражённые экспоненциальные фильтры полного r. |
| P_RG2 | 0.90 | Для каждого фиксированного eta>0 ядро K2−eta G не PSD: физический дефект имеет далёкую отрицательную диагональ. |
| P_RG3 | 0.95 | Полный остаток сохраняет digamma, Mellin-нормировку и весь Gram; его отказ не является отрицательной V. |

## 3. Взаимность ставит Mellin-интеграл на правильную полуплоскость

Сохраняем \(A=A_{\rm norm}\), \(\lambda_n=\pi n^2\), исходные r, L, f и Fourier-конвенцию задания. Обозначим
\[
M(s)=\int_0^\infty t^{s-1}r(t)\,dt,
\qquad B(q)=\int_0^\infty v^{q-1}L(v)\,dv,\quad\Re q>0.
\tag{RG2}
\]
**B не является граничной формой**; это скалярный Mellin-интеграл L. Граничную поправку обозначаем только \(\mathcal B\).

Полные хвосты r и взаимность делают M целой функцией s и дают
\[
M(s)=M(5/2-s),\qquad
B(q)=\Gamma(q)M(1-q)=\Gamma(q)M(3/2+q)
=2\Gamma(q)\xi(1+2q).
\tag{RG3}
\]
Второе равенство следует из абсолютного Fubini и Gamma-интеграла: для \(a=\Re q>0\) интеграл модуля равен \(\Gamma(a)\int t^{-a}r(t)dt<\infty\). Взаимность используется **до** применения безнулевого Euler-домена. При Re q>0 аргумент \(1+2q\) имеет действительную часть больше 1. Поэтому B не имеет нулей на этой полуплоскости. Это не предположение RH.

Нужная линия и точная нормировка:
\[
q_u=\frac34-\frac{iu}{2},\qquad F_2(u)=F(u+2i)
=\frac{B(q_u)}{2A\Gamma(q_u)}.
\tag{RG4}
\]
Действительно, прямой переход \(t=e^{2x}\) даёт \(F_2(u)=M(9/4-iu/2)/(2A)\), а взаимность переводит этот аргумент в \(1/4+iu/2=1-q_u\).

У L в нуле \(L(v)=1+O(v)\). При \(v\to\infty\) полный sinh product даёт
\(L(v)=O(v e^{-2\sqrt{\pi v}})\). На компактных подмножествах Re q>0 эти оценки интегрируемы с любым фиксированным множителем \(|\log v|^j\). Поэтому B голоморфна, а её q-производные получаются под интегралом. Никакого продолжения расходящегося интеграла не используется.

Положив \(\psi=\Gamma'/\Gamma\), получаем точное выражение потребителя:
\[
R_2(u)=\frac12\left[\frac{B'(q_u)}{B(q_u)}-\psi(q_u)\right].
\tag{RG5}
\]
Множитель 1/2 происходит из \(dq_u/du=-i/2\), поскольку \(R_2=i\,\partial_u\log F_2\). Удаление digamma меняло бы потребителя. Формулы (RG2)–(RG5): `[ABSTRACT][PAPER]`.

## 4. Одна конкретная положительная карта из S1

Возьмём полный источник в самом Mellin-весе:
\[
\rho_q(v)=\frac{v^{q-1}L(v)}{B(q)},\quad
J_n(q)=\int_0^\infty\frac{v^{q-1}L(v)}{\lambda_n+v}\,dv,
\quad b_n(u)=\frac{J_n(q_u)}{B(q_u)}.
\tag{RG6}
\]
При комплексном q функция \(\rho_q\) не положительная плотность. Мы **не** применяем к ней Jensen. Положительность ниже идёт от Hermitian-конгруэнции S1 с сопряжённым весом в первом аргументе.

Определим
\[
\begin{split}
\mathcal G(u,v)
&=\frac{1}{4+i(u-v)}
\int_0^\infty\!\int_0^\infty
 \overline{\rho_{q_u}(s)}G_{\rm src}(s,t)\rho_{q_v}(t)\,ds\,dt\\
&=\frac{2\sum_{n\ge1}\overline{b_n(u)}b_n(v)}{4+i(u-v)}.
\end{split}
\tag{RG7}
\]
Это выбранный ansatz, а не утверждение, что всякая возможная карта обязана иметь такой вид. Полный вес L связывает его с Mellin-интегралом (RG2); нормировка B связывает с отношением (RG5); знаменатель совпадает с S2.

На нашей линии, \(a_0=3/4\),
\[
|J_n(q_u)|\le\frac{B(a_0)}{\lambda_n},\qquad
\sum_n|b_n(u)|^2\le
\frac{B(a_0)^2}{|B(q_u)|^2}\sum_n\lambda_n^{-2}<\infty.
\tag{RG8}
\]
Кроме того, на положительных s,t
\(0<G_{\rm src}(s,t)\le2\sum\lambda_n^{-2}\). Эти оценки разрешают оба интеграла, обмен с полной суммой и локальную равномерность по u,v. Деление на B требует только его ненулевого значения при каждом конечном наборе узлов. Глобальная ограниченность \(1/B\) не утверждается.

Явная общая карта в \(\ell^2(\mathbb N)\otimes L^2(0,\infty;d\tau)\):
\[
\Theta_u(n,\tau)=\sqrt2\,b_n(u)e^{-2\tau+iu\tau}.
\]
Она имеет Gram-ядро \(\mathcal G\). Поэтому для каждого конечного комплексного a
\[
\sum_{i,j}\overline{a_i}\mathcal G(u_i,u_j)a_j
=2\sum_n\int_0^\infty e^{-4\tau}
 \left|\sum_j a_j b_n(u_j)e^{iu_j\tau}\right|^2d\tau\ge0.
\tag{RG9}
\]
Объект построен без неизвестного квадратного корня из K2. S1 действительно использован, и все его моды сохранены. (RG6)–(RG9): `[ABSTRACT][PAPER]`.

## 5. Полный остаток после карты, а не неявное отождествление

Для любого фиксированного \(\eta\ge0\) поставим \(\Delta_\eta=K_2-\eta\mathcal G\). Подстановка (RG5)–(RG7) даёт **вычислимое по источнику** выражение:
\[
\boxed{
\Delta_\eta(u,v)=\frac{1}{4+i(u-v)}
\int_0^\infty\!\int_0^\infty
\overline{\rho_{q_u}(s)}\rho_{q_v}(t)
\left\{\frac{\log s+\log t-\overline{\psi(q_u)}-\psi(q_v)}2
            -\eta G_{\rm src}(s,t)\right\}ds\,dt.}
\tag{RG10}
\]
Оба логарифма и обе digamma-части обязательны. Нормировка \(\int\rho_q=1\) объясняет постоянные члены, но не даёт знака выражения в фигурных скобках. Абсолютная интегрируемость следует из логарифмических оценок §3 и (RG8). Здесь нет условно суммируемых разностей.

Для проверки сохранения архимедовых и арифметических слагаемых (RG5) по точному T совпадает с
\[
R_2(u)=\frac1{5/2-iu}+\frac1{3/2-iu}-\frac{\log\pi}2
+\frac12\psi(5/4-iu/2)
-\sum_{m\ge2}\frac{\Lambda(m)}{m^{5/2-iu}}.
\tag{RG11}
\]
Оба полюса и все простые степени присутствуют. Ряд абсолютно сходится, поскольку \(\Lambda(m)\le\log m\) и \(\sum(\log m)m^{-5/2}<\infty\). Нельзя подставить в (RG10) одну \(\psi(q_u)\) вместо всего R2 или отождествить \(A_{\rm src}\) с \(\!B'/B\).

Одна запись (RG10) ещё не уменьшает знакового пробела. Новое отрицательное заключение ниже относится именно к этой полной поправке. (RG10)–(RG11): `[ABSTRACT][PAPER]`.

## 6. Точный физический образ построенного Gram

### 6.1. Экспоненциальные фильтры того же полного источника

Положим при t>0
\[
v_n(t)=\int_0^t r(t-y)e^{-\lambda_n y}\,dy,
\qquad \phi_n(x)=\frac1A e^{-5x/2}v_n(e^{-2x}),\quad x\in\mathbb R.
\tag{RG12}
\]
Каждое v_n положительно. Это **ненормированный резольвентный фильтр**, не замена r новым терминальным законом. Его Laplace-преобразование равно \(L(s)/(\lambda_n+s)\). Взаимность v_n не предполагается.

Два абсолютных Fubini и подстановка \(t=e^{-2x}\) дают
\[
\begin{split}
J_n(q_u)&=\Gamma(q_u)\int_0^\infty t^{-q_u}v_n(t)\,dt,\\
F_2(u)b_n(u)&=\frac{J_n(q_u)}{2A\Gamma(q_u)}
=\int_{\mathbb R} e^{2x}\phi_n(x)e^{-iux}\,dx.
\end{split}
\tag{RG13}
\]
Проверка степеней: \(2q_u-2=-1/2-iu\), поэтому якобиан действительно даёт \(e^{-x/2}v_n(e^{-2x})/A=e^{2x}\phi_n(x)\). Это точная карта, не асимптотическая модель.

### 6.2. Один полный бюджет для всех резольвентных мод

Отделение первой Gamma(2,pi) переменной в r только для оценки даёт
\[
0<r(t)\le4\pi^2 t e^{-\pi t},\quad t>0.
\]
Коэффициент 4 следует из **полного** произведения остатка
\(\prod_{n\ge2}(1-n^{-2})^{-2}=4\). Взаимность даёт дополнительно
\(r(t)\le4\pi^2t^{-7/2}e^{-\pi/t}\). Следовательно, можно взять
\[
c_*=\pi/4,\qquad
C_r=4\pi^2e^{\pi/4}\max\{1,(14/(3\pi e))^{7/2}\},
\]
так что для всех t>0
\[
 r(t)\le C_r e^{-c_*(t+1/t)},\qquad
 0<v_n(t)\le\frac{C_r}{\lambda_n-c_*}e^{-c_*(t+1/t)}
 \le\frac{4C_r}{3\lambda_n}e^{-c_*(t+1/t)}.
\tag{RG14}
\]
Для первой оценки отдельно используем t>=1 и t<=1; максимум \(z^{7/2}e^{-3\pi z/4}\) равен \((14/(3\pi e))^{7/2}\). Для второй в свёртке пишем z=t-y, используем \(1/z\ge1/t\) и интегрируем \(e^{-(\lambda_n-c_*)y}\). Ни малый конец, ни бесконечность, ни оставшиеся Gamma-переменные не удалены.

Отсюда
\[
0<\phi_n(x)\le\frac{4C_r}{3A\lambda_n}
 e^{-5x/2-c_*(e^{2x}+e^{-2x})}.
\tag{RG15}
\]
Это одновременно оплачивает все фиксированные экспоненциальные веса по x, сумму квадратов по n и непрерывность последующих ядер. В частности \(\sum_n\|\phi_n\|_2^2<\infty\). Для локальной непрерывности достаточно доминирования (RG15), непрерывности свёртки и теоремы о пределе под интегралом; производные не подставляются без необходимости.

### 6.3. Fourier-образ с буквальной физической границей

Определим положительное пространственное ядро
\[
\boxed{V_G(x,y)=2\sum_{n\ge1}\int_0^\infty
          \phi_n(x+X)\phi_n(y+X)\,dX.}
\tag{RG16}
\]
Все конечные комплексные строки дают сумму квадратов. Граница интеграла остаётся X=0.

С \(g_n(x)=e^{2x}\phi_n(x)\), (RG13) и точным интегралом Cauchy получаем
\[
\begin{split}
\overline{F_2(u)}\,\mathcal G(u,v)\,F_2(v)
&=\int_{\mathbb R^2} e^{2(x+y)}V_G(x,y)e^{iux-ivy}\,dx\,dy,\\
\overline{F_2(u)}\,\Delta_\eta(u,v)\,F_2(v)
&=\int_{\mathbb R^2} H_\eta(x,y)e^{iux-ivy}\,dx\,dy,\\
H_\eta(x,y)&=e^{2(x+y)}[V(x,y)-\eta V_G(x,y)].
\end{split}
\tag{RG17}
\]
Это сохраняет ровно ту же диагональную конгруэнцию, что T; её обратимость нужна лишь на конечной строке.

Полный L1-бюджет для нового ядра можно проверить без осциллирующих интегралов. Поскольку \(g_n\ge0\), (RG13) при u=0 даёт
\(\|g_n\|_1=J_n(3/4)/(2A\Gamma(3/4))\le F_2(0)/\lambda_n\). Поэтому Tonelli даёт
\[
\int_{\mathbb R^2}e^{2(x+y)}V_G(x,y)\,dx\,dy
=\frac12\sum_n\|g_n\|_1^2
\le\frac{F_2(0)^2}{2}\sum_n\lambda_n^{-2}<\infty.
\tag{RG18}
\]
Множитель 1/2 равен \(2\int_0^\infty e^{-4X}dX\). Для исходной V абсолютный бюджет из T равен не более
\(\frac14\int_{\mathbb R^2}|x+y|f(x)f(y)e^{2(x+y)}dxdy<\infty\).
Таким образом H_eta непрерывно и принадлежит L1(R²); его Fourier-образ ограничен. Обмены в (RG17) полностью оплачены. Весь §6: `[ABSTRACT][PAPER]`.

## 7. Строгий отрицательный дефект на самой theta

При x=-R, R>0, чётность исходного f даёт
\[
0<V(-R,-R)=2\int_{-R}^\infty y f(y)^2dy
=2\int_R^\infty y f(y)^2dy\longrightarrow0.
\tag{RG19}
\]
Напротив, у точного положительного образа
\[
V_G(-R,-R)=2\sum_n\int_{-R}^\infty\phi_n(y)^2dy
\longrightarrow2\sum_n\|\phi_n\|_2^2>0.
\]
Существование и конечность последнего предела следуют из Tonelli и (RG15); строгая положительность — уже из n=1. Эти пределы: `[COFINAL_FAMILY][PAPER]`. Это не предел усечённых источников.

Для KILL нужен строгий верхний запас, а не только несовпадение пределов. Определим из полного r
\[
d_*=2\int_0^1 e^{-5y}v_1(e^{-2y})^2dy>0,
\quad C_V=8\pi^3\left(\frac9{2\pi e}\right)^{9/2}.
\]
Для R>=0 имеем \(V_G(-R,-R)\ge d_*/A^2\). Из \(r(t)\le4\pi^2te^{-\pi t}\), подстановки t=e^(2y) и \(\log t\le t\) при t>=1 получаем
\[
V(-R,-R)\le\frac{8\pi^4}{A^2}
\int_{e^{2R}}^\infty t^{7/2}\log t\,e^{-2\pi t}dt
\le\frac{C_V}{A^2}e^{-\pi e^{2R}}.
\]
В последней оценке использован максимум \(t^{9/2}e^{-\pi t}\) на t>0, а затем точный интеграл \(e^{-\pi t}\).

Для каждого eta>0 выберем любой конечный R_eta>=1, удовлетворяющий проверяемому условию
\(C_Ve^{-\pi e^{2R_\eta}}\le\eta d_*/2\). Такое R существует независимо от знака V. Тогда для всех R>=R_eta
\[
\boxed{V(-R,-R)-\eta V_G(-R,-R)
\le-\frac{\eta d_*}{2A^2}<0.}
\tag{RG20}
\]
Параметры d_* и R_eta определены источником и положительным интегралом v1, не неизвестным нулём xi. Численные значения не заявлены. При этом сама V в (RG19) **положительна**, что непосредственно проверяет область отрицательного заключения.

## 8. Из отрицательного физического дефекта — конечная строка потребителя

Нужно ещё вернуть результат к частотным узлам S2. Нельзя назвать узел -R частотой u и пропустить Fourier-переход.

Зафиксируем eta,R как в §7 и x0=-R. Из (RG20)
\[
H_\eta(x_0,x_0)\le-\gamma,
\qquad\gamma=e^{-4R}\frac{\eta d_*}{2A^2}>0.
\tag{RG21}
\]
Возьмём неотрицательную гладкую функцию a_epsilon с интегралом 1 и носителем в малой окрестности x0. По непрерывности H_eta, при достаточно малом epsilon,
\[
\int_{\mathbb R^2}\overline{a_\epsilon(x)}H_\eta(x,y)a_\epsilon(y)dxdy
\le-\gamma/2.
\tag{RG22}
\]
Это честный тест полного signed-ядра, а не проверка одного отброшенного слагаемого.

Положим \(\widehat a_+(v)=(2\pi)^{-1}\int a_\epsilon(y)e^{ivy}dy\), так что
\(a_\epsilon(y)=\int\widehat a_+(v)e^{-ivy}dv\). Функция \(\widehat a_+\) принадлежит классу Schwartz. Из (RG17), H_eta in L1 и абсолютного Fubini следует равенство левой части (RG22) и
\[
\int_{\mathbb R^2}\overline{\widehat a_+(u)}W_\eta(u,v)
       \widehat a_+(v)du\,dv,
\quad W_\eta=\overline{F_2}\,\Delta_\eta F_2.
\]
Поскольку \(\|W_\eta\|_\infty\le\|H_\eta\|_1\), отсечение Schwartz-хвоста меняет этот интеграл сколь угодно мало. Явный бюджет при \(\ell=\|\widehat a_+\|_1\), хвосте \(e_M=\int_{|u|>M}|\widehat a_+(u)|du\), не превосходит \(2\|H_\eta\|_1\ell e_M\). После выбора M непрерывность на квадрате [-M,M]² разрешает конечные Riemann-суммы.

Выбираем отсечение и затем сетку лишь как **доказательство существования конечной аппроксимации**, чтобы суммарная ошибка была меньше gamma/4. Никакая численная сетка не запускается. Для некоторых конечных узлов u_j и коэффициентов beta_j получаем
\[
\sum_{i,j}\overline{\beta_i}W_\eta(u_i,u_j)\beta_j
<-\gamma/4.
\tag{RG23}
\]
Теперь \(a_j=F_2(u_j)\beta_j\) — допустимая конечная комплексная строка. Все F2(u_j) ненулевые; глобального обратного множителя нет. По (RG17)
\[
\boxed{\sum_{i,j}\overline{a_i}\Delta_\eta(u_i,u_j)a_j
<-\gamma/4<0.}
\tag{RG24}
\]
Это доказывает (RG1), включая произвольную фиксированную eta>0. Ранг и численные частотные узлы не оценены. Доказывается существование, а не приводится выдуманный вычисленный свидетель. Весь §8: `[ABSTRACT][PAPER]`.

Если бы \(K_2=\eta\mathcal G+\mathcal B\) с PSD-ядром B, левая часть (RG24) была бы B[a]>=0. Поэтому никакая неотрицательная поправка, сколь угодно большой ранг которой разрешён, не чинит **этот** перенос. Добавление signed-поправки (RG10) верно, но уже не является положительным доказательством.

## 9. Все края и сильнейшие возражения

**Mellin-концы.** В v=0 используется Re q=3/4>0 и L(v)=1+O(v); в v=infinity — полный sinh-tail. Логарифмы в (RG10) оплачены теми же мажорантами. Замена Re q на отрицательную величину без взаимности дала бы расходящийся Mellin-интеграл в нуле; такая подмена здесь не сделана.

**Концы исходной свёртки.** v_n определено на всём [0,t]. Предел r в нуле нулевой; оценка (RG14) одновременно контролирует оба конца. Дополнительные endpoint distributions или отсечение малых t не вводились.

**Физическая граница X=0.** Она сохранена в (RG16) и исходной V. При x=-R становится нижним концом y=-R; интервал [-R,0] не выброшен. Только у V чётность даёт точное сокращение со следующим участком. У V_G интеграл остаётся суммой квадратов. Значения подынтегральных выражений при X=0 вообще ненулевые: у V это (x+y)f(x)f(y), у V_G — 2 sum phi_n(x)phi_n(y). Никакое нулевое граничное условие не назначено.

**Бесконечность X и сумма по n.** (RG15), (RG18) оплачивают каждый использованный предел и сумму. Нет утверждения, что одного конечного числа source modes достаточно для точного K2. Использование n=1 в (RG20) — нижняя оценка уже положительной суммы с сохранением остальных мод, не замена источника.

**«Выбранная карта не единственная».** Верно. Это наиболее важная граница результата. Запрос разрешает искать одну карту, но не даёт права объявить её обязательной. Здесь исключена конкретная \(\rho_q\)-конгруэнция с Cauchy-фактором и PSD-добавкой. Другой интегральный вес, коррелированные выходные каналы, иная source-built карта либо signed-компенсация требуют нового доказательства. Они не опровергнуты.

**«Получилась лишь старая ловушка с положительной энергией».** Положительность сама по себе действительно была бы недостаточна. Новое содержание — точная карта (RG6)–(RG9), её полный физический образ (RG12)–(RG18), и исходный строгий отказ (RG20)–(RG24) для любого положительного коэффициента. Это проверка заданного нового G_src, не применение прежнего no-go к похожему объекту.

**«Не выполнен TN-infinity у отрицательного контроля».** Посторонний контроль не использован. r буквально исходная theta и имеет оба заданных свойства. Отрицателен не её V, а разность с конкретным перенесённым Gram. Поэтому вывод об общей недостаточности совместных TN-infinity и reciprocity здесь отсутствует.

**«Отрицательная Delta означает отрицательную V».** Нет: даже на использованном пространственном диагональном тесте V>0 по (RG19). Разность отрицательна, поскольку положительный кандидат слишком велик. В (RG24) отрицательно K2−eta G, не K2.

**Нулевые и повторные строки.** Все построенные карты линейны по одной конечной строке. Нулевой вход даёт нули. Повторные узлы объединяются сложением коэффициентов до всех аппроксимаций. Число физических узлов не отождествляется с числом source rates.

## 10. Где именно работают исходные свойства

| Переход | Использованное свойство | Полученный вывод и предел его действия |
|---|---|---|
| S1 -> RG7–RG9 | Полный резольвентный Gram, lambda_n=pi n², sum lambda_n^(-2)<infinity | Независимая положительность конкретного выходного Gram; не знак K2 |
| RG2 -> RG3–RG4 | Точная взаимность r(1/t)=t^(5/2)r(t) | Нужная Mellin-линия q=3/4−iu/2; точное совпадение нормировки с F(u+2i) |
| Ненулевые B и F2 | Единственность разложения на простые, Euler product при Re s>1, Gamma без нулей | Законность конечных делений на линии Re s=5/2; не положительность всех K2-матриц |
| RG13 | Laplace-конволюция того же r с exp(-lambda_n t), Gamma-интеграл | Точный физический образ каждой резольвентной колонки |
| RG14–RG18 | Полный квадратный спектр, product_(n>=2)(1−n^(-2))^(-2)=4, взаимность | Двусторонний tail-budget и суммируемость всех мод |
| RG19–RG20 | Взаимность именно исходной theta, то есть чётность f; ненулевая положительная колонка | Строго отрицательный полный дефект выбранного переноса |
| RG23–RG24 | Точные Fourier-конвенции, конечная ненулевая конгруэнция | Возврат отказа на буквальные конечные строки S2 |

Единственность разложения на простые действительно использована для **ненулевого делителя**, а не как новый механизм знака. TN-infinity остаётся верным входом, но его ordered minors не потребляются после Mellin-конгруэнции. Степенной наклон не объявляется TN-preserver. Другим phi_n не приписана взаимность r. Все строки этой таблицы: `[ABSTRACT][PAPER]`.

## 11. Ledger, зависимости и минимальный оставшийся объект

| Утверждение | Статус | Scope / verifier |
|---|---|---|
| S1 и принятый all-test consumer T | Сохранённые входы | ABSTRACT / PAPER |
| Правильная отражённая Mellin-линия и RG5 | Доказаны §§3–5 | ABSTRACT / PAPER |
| Общий положительный Gram RG7 и его область | Доказаны §4 | ABSTRACT / PAPER |
| Полный signed-остаток, оба полюса, простые и digamma | Сохранены RG10–RG11 | ABSTRACT / PAPER |
| Точный физический образ и полный модовый бюджет | Доказаны §6 | ABSTRACT / PAPER |
| Различные диагональные пределы при R->infinity | Доказаны §7 | COFINAL_FAMILY / PAPER |
| Строгая отрицательная верхняя огибающая дефекта | Доказана RG20 | ABSTRACT / PAPER |
| Отрицательная конечная строка K2−eta G для каждого eta>0 | Доказана §8 | ABSTRACT / PAPER |
| Полная V>=0 и все K2 PSD | Не доказаны и не опровергнуты | ABSTRACT / CONDITIONAL |

```yaml
DOWNSTREAM_CONSUMER: exact_K2_all_finite_complex_PSD_then_T_Weil_and_original_V
ACTUAL_CONSUMER_REQUIREMENT: K2_PSD_on_every_finite_real_frequency_node_list
ORIGINAL_REQUESTED_OBJECT: positive_transport_from_actual_G_src_and_reciprocity_to_exact_K2
ORIGINAL_OBJECT_IS: NOT_NECESSARY_as_a_specific_proof_method
TESTED_INTERFACE: normalized_L_weighted_Mellin_congruence_tensor_Cauchy_plus_PSD_boundary
TESTED_INTERFACE_IS: NOT_NECESSARY_for_full_V_sign
KNOWN_WEAKER_OR_DIFFERENT_INTERFACES:
  - another_source_built_common_Gram_with_proved_exact_K2_identity
  - independently_proved_full_signed_lower_bound_with_the_same_consumer
FAILURE_TYPE: COUNTEREXAMPLE
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: strict_upper_envelope_of_full_map_defect_and_finite_Fourier_transfer
KILL_EVIDENCE_REF: RG20_RG21_RG22_RG23_RG24
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_TESTED_INTERFACE_ONLY_PENDING_REVIEW
NOVELTY_AXIS: explicit_resolvent_Mellin_feature_transport_and_reciprocal_diagonal_mismatch
WIDER_ROUTE_STATUS: RESEARCH_DEBT
WIDER_ROUTE_REOPEN_TRIGGER: genuinely_different_source_map_preserving_the_physical_signed_pair_and_all_boundaries
NAMED_MAP_REOPEN_TRIGGER: demonstrated_error_in_RG13_RG17_or_the_strict_defect_argument
FULL_V_MINIMAL_MISSING_SIGN: complete_original_K2_or_equivalently_complete_V_on_all_finite_complex_rows
ROUTE_FAMILY_KILL: false
RH_CLAIM: false
```

**Полный список зависимостей доказательства отказа:** заданные полные r и L; взаимность r; принятая Mellin/Fourier-нормировка и kernel identity T7; Gamma-интеграл; Euler product в абсолютной полуплоскости; Tonelli/Fubini, доминированные пределы, Fourier inversion для гладких компактных функций и конечные Riemann-аппроксимации. Никаких нулевых гипотез, GGC-предпосылок, положительности V, ограниченного обратного Fourier-множителя или знака бесконечного остатка нет.

После (RG10) формула K2=G+Delta точна, но требование неотрицательности **суммы** остаётся прежним конечным потребителем. Мы не объявляем его новым Y. Для выбранного положительного boundary-ремонта пробел уже не открыт: он опровергнут.

Два представления для оставшегося полного знака фиксируются без запуска новых исследований. **R1:** точный нормированный Mellin-баланс (RG10) вместе с (RG7); стоимость проверки объекта 2/5, потенциальная решающая сила полного signed-сравнения 5/5, стоимость такого сравнения неизвестна. **R2:** исходный физический V и проверка его взаимного сокращения до любой положительной факторизации; стоимость диагонального фильтра 1/5, решающая сила против данной карты 5/5, но для полного знака всех смешанных строк пока нет нового бюджета. Это оценки выбора теста, не вероятности RH.

**DISCRIMINATOR:** для сомнительного нулевого дефекта использовать d_*>0 и условие C_V exp(-pi exp(2R))<=eta d_*/2, затем строгий запас RG20. Для отрицательной самой V потребовалась бы верхняя огибающая полного K2 или полного V без вычитания eta G; здесь такой огибающей нет.

## 12. Closeout и проверочная передача

**Что уменьшилось:** конкретный новый резольвентный кандидат больше не чёрный ящик. Его точный physical kernel и полная поправка известны; невозможность исправления положительной добавкой доказана на исходном источнике.

**Что не уменьшилось:** знак всей V. Это фильтр одного достаточного механизма, а не новый source-sign supplier и не RH-прогресс.

**Что не повторять:** ту же нормированную Mellin/Cauchy-конгруэнцию с другим постоянным положительным коэффициентом; объявление её остатка положительной boundary-формой; идентификацию A_src с Mellin-log-derivative; отрицательный дефект как отрицательную V; увеличение source-уровней или повтор EDGE/LP/tilted-PF.

**Судьба предсказаний:** P_RG1 confirmed, RG8 и RG12–RG18; P_RG2 confirmed, RG20–RG24; P_RG3 confirmed, RG10–RG11 и точная область RG1. Регистрация не переписана. Численных вычислений theta, квадратур, сканирования нулей и матриц не было.

**Один следующий Codex joint:** независимый аудит именно этого Markdown с критерием `ACCEPT_NORMALIZED_MELLIN_CAUCHY_MAP_OBSTRUCTION_ONLY`. Проверить q_u, коэффициенты 2 и A в RG4/RG13, обе Fourier-фазы RG17, модовый бюджет RG14/RG18, диагональный строгий запас RG20 и перенос отрицательности RG22–RG24 на конечную частотную строку. Ошибка должна быть названа конкретной формулой. Приём не меняет V/RH-state и не запускает новую цепочку предположений.

**Memory:** target=G_src to literal Weil atom kernel; result=FALSIFICATION_PROGRESS; invariant=positive Mellin-congruence preserves a whole-line norm that the original reciprocal mixed flux cancels; forbidden move=repair the same Gram by adding a PSD boundary; next decisive test=independent audit of RG13/RG17/RG24. Оценка полезности фильтра 4/5; близость доказательства RH этим не оценивается. Счётчики истории не восстановлены произвольно и не сброшены.

**Доставка:** записывается только новый назначенный путь из YAML, после чтения свежей HEAD; обычный Contents API commit, без force и правок чужих файлов. Commit SHA и Git blob проверяются readback после записи; самоссылочный commit SHA в собственное содержимое не включается. Diff должен показывать только один новый файл.

**Верификация:** PAPER-кандидат до независимого приёма. Lean-исходников нет, Lean/lake не запускались, профиль аксиом не получен; фиктивной команды Lean-gate нет. Независимый приём относится только к точной карте, её полному signed-образу и scoped no-go. Полная V и RH не доказаны и не опровергнуты.
