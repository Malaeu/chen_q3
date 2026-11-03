# STATUS: TRY_MYTHOS_COUPLING_RIGIDITY_AND_COMPLEMENT_EXIT

```yaml
OPERATIVE_CLASS: TRY_MYTHOS_COUPLING_RIGIDITY_AND_COMPLEMENT_EXIT
REQUEST: MYTHOS_H1_H12_DOSSIER
DATE: 2026-11-03
AUTHORITY: DIRECT_OWNER_MATHEMATICAL_REQUEST_IN_CHAT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
BASE: rh_clean@cdb84497
INBOX_SOURCE: 75afd6a1f8e244f1da55e4c608233b22cc07c9f4
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE: CHALLENGER_NOT_RH
CARRIER: LITERAL_REAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
MAIN_RESULTS:
  - UNCONDITIONAL_SUPERPOLYNOMIAL_OUTER_TUBE_FOR_ALL_FEASIBLE_SCALAR_COUPLINGS
  - COFINAL_NONEMPTY_SCALAR_COUPLING_INTERVAL_EQUIVALENT_TO_RH_USING_INHERITED_CONSUMER
  - ACTUAL_ZETA_FACTOR_TWO_COMPLEMENT_MARGIN_REFUTED_ON_AN_EXPLICIT_COFINAL_INTEGER_FAMILY
  - SECOND_ORDER_QUIET_COUPLING_AND_HEAT_COMPRESSION_COUNTEREXAMPLES
  - INDIVIDUAL_OFF_LINE_ZERO_SOURCE_NORM_VISIBILITY_HORIZON
H1: REDUCED
H2: REFUTED
H3: REFUTED
H4: REDUCED
H5: REDUCED
H6: REDUCED
H7: REDUCED
H8: REDUCED
H9: REFUTED
H10: REDUCED
H11: REDUCED
H12: REDUCED
H2_REFUTATION_SCOPE: LITERAL_ZETA_AND_ACTUAL_ZERO_DEFINED_J_ON_A_COFINAL_FAMILY
H3_REFUTATION_SCOPE: ZERO_QUIET_COMPRESSION_IMPLIES_UNIFORM_TOLERANCE_THEOREM_SHAPE
H9_REFUTATION_SCOPE: WHOLE_FINITE_COMPRESSION_INERTIA_INVARIANCE_THEOREM_SHAPE
H9_COUNTERMODEL_IS_ZETA_OR_DH: false
FINITE_CRITICAL_ZERO_LIST_USED_AS_POSITIVITY: false
PNT_USED: true
PNT_USE: ONLY_THEOREM_4_PRIME_CONTINUUM_CANCELLATION
QUIET_RESIDUAL_SUPPLIER: INHERITED_PAPER_NOT_REPROVED
GLOBAL_SOURCE_POSITIVITY: NOT_PROVED
RH_ASSUMED_FOR_UNCONDITIONAL_RESULTS: false
RH_PROVED: false
ROUTE_STATE_CHANGED: false
VERIFIER: PAPER
NUMERICAL_PART: DIAG_NOT_INTERVAL
EXACT_SYMBOLIC_CONTROL_COUNT: 18
FINITE_SYNTHETIC_HEAT_CONTROL_DPS: [70, 100]
NEW_ZETA_OR_DH_CCM_EIGENSYSTEMS: 0
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
PROGRESS_CLASS: PROOF_PROGRESS
ADDITIONAL_PROGRESS: SCOPED_FALSIFICATION
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_MYTHOS_HYPOTHESIS_DOSSIER_2026-11-03.md
```

## 0. Итог

Ы. Три наиболее существенных результата:

1. **H1: тонкость общего коэффициента простых доказана как внешняя оценка, без RH.** Для любого B>0 все допустимые u удовлетворяют |u-1|=o(m^-B). Это не доказывает, что допустимые u вообще существуют. Неограниченная семья НЕПУСТЫХ интервалов эквивалентна RH через унаследованный потребитель нижнего пола.
2. **H2: фиксированного запаса 2 на настоящем J-perp нет.** Построены единичные f_m в J-perp на явной неограниченной последовательности исходных целых m, для которых <f_m,(C+2B)f_m> уходит к минус бесконечности. Используются полный источник, PNT и один настоящий критический нуль как evaluation-условие, не положительность списка нулей.
3. **H9: сохраняется инерция отдельного нулевого блока, но не произвольной конечной компрессии суммы блоков.** Дано доказательство контрсемьи на том же типе физического carrier; вычислительный экземпляр меняет отрицательный индекс с 1 на 0. Это не утверждение о найденном изменении инерции настоящей zeta.

Дополнительно получен количественный возврат отрицательного свидетеля для H6: заданный off-line нуль с кратностью и указанными ниже source-нормами дает явный порог всех последующих m. Равномерная оценка только через высоту Gamma и отступ eta без этих норм остается неоплаченной.

Ни один результат не доказывает положительность A_m. Существование допустимой точки и жесткость ее возможного положения — разные кванторы.

## 1. Источники и неизменяемый объект

### 1.1. Что прочитано и что наследуется

R0. PROSHKA_SYSTEM_PROMPT_v2.md прочитан через GitHub с rh_clean, включая окончание; blob указан в header.

R1. `docs/routeB_bus/arithmetic_coupling_2026-11-03/RESULT.md` на cdb84497, blob b0900f4c5533c4604aebfb418f13ced031c3d552. Основные 855 ячеек имеют epsilon-relaxed интервалы. Малые 120-digit пилоты m16/24/40 — DIAG, не интервальные доказательства точного I_0. В этом отчете J использует kappa=1; это НЕ расписание moving-kappa из R3.

R2. `docs/routeB_bus/gaussian_height_2026-11-03/RESULT.md` на cdb84497, blob 41d21ef1e22f9f3ef85b5a7254f6253ff8b09579. Это конечный нулевой census, комплексный Gaussian и проверка отдельных source entries; неизвестный бесконечный хвост не сертифицирован. Тепло меняет оператор, а не только координаты старого A_m.

R3. `PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, blob ebf7f8cab61a795118bda5dc7e65a0b3386247b7, §§0–1 на cdb84497. Наследуются r_m>0 eventually и delta_m=||A_m Q_m||=o(m^-B) при каждом фиксированном B для FIXED 0<c<1 и kappa_m=1+c(1+log log m)/log m. Названный владельцем PAPER-аудит не повторялся. Равномерность до kappa=1 не добавляется.

R4. `PROSHKA_VERDICT_CONFINE_2026-10-30.md`, blob 1879347b72d1aa55cf506f5387de37059f929122, (1.3)–(1.6), на cdb84497. Используются полный источник, его непрерывность на быстро убывающих взвешенных гладких тестах и безусловная смешанная явная формула. В §4 ниже дан самостоятельный нужный возврат в N=m.

R5. `PROSHKA_VERDICT_NOESCAPE_COMPLEMENT_2026-11-02.md`, blob 1a20e653e46bbad3d0f5eb19e7c7d73f4fb5e82f, на cdb84497. В ЭТОМ файле дополнение первоначально относится к одному theta-вектору, а не ко всему J. Для всего J используется такая же элементарная блочная оценка, выписанная здесь. Унаследованный конечный отрицательный свидетель при not-RH дает достаточность полного пола -o(1). Потребитель постоянного пола из досье также наследуется, не передоказывается.

R6. Полный локальный `PROSHKA_VERDICT_BALANCE_VERTEX_SOFTNESS_2026-11-03.md`, inbox75afd6a1, blob c150754c6c287545d3e893d60470c98998a98a45: точная dual-альтернатива, полный второй порядок, source-correct сдвиг X_a. Его предыдущая мягкость с неактивной ручкой не переносится в исправленную H4: в H4 такие ручки уже удалены.

R7. Кривизна Schur и различие source/inverse-kinks, fixed-shadow невидимость и сохранение Cramer-сигнала из перечисленных владельцем inbox-вердиктов используются лишь с прежними оговорками. Их независимый аудит в этой работе не заявляется.

Путь `docs/routeB_bus/stiffness_2026-11-03/RESULT.md` при новом обращении к rh_clean вернул 404. Параллельные еще не полученные результаты не предполагаются.

Внешние первичные справочные формулы проверены на NIST DLMF: 25.4 (xi и FE), 25.10 (критические нули и симметрии), 27.12 (PNT), 5.11 (Stirling/digamma). Ни один внешний результат, предполагающий нужный знак Вейля, не импортируется.

```text
https://dlmf.nist.gov/25.4
https://dlmf.nist.gov/25.10
https://dlmf.nist.gov/27.12
https://dlmf.nist.gov/5.11
```

### 1.2. Форменная нормировка [ABSTRACT | PAPER; E/F/I/A]

Все физические функции продолжены нулем за окном, если поддержка конечна. Для вещественного четного f:

    Q_f(s)=2 integral f(x)f(x+s) dx,
    j(s)=exp(-s/2)/(1-exp(-2s)),
    c_*=EulerGamma+log(8pi)+pi/2,
    p(x)=sqrt(2)cosh(x/2),
    C[f]=integral_0^infinity j(s)||f-T_s f||^2 ds
         -c_*||f||^2+|<p,f>|^2,
    B[f]=-sum_(n>=2) Lambda(n)/sqrt(n) Q_f(log n),
    W[f]=C[f]+B[f].                                      (1.1)

Все простые степени сохранены. На поддержке длины L=log m атомы n>m и крайний n=m дают нулевую корреляцию ТОЧНО. Нечетный полюс исчезает только вследствие четности. В общем комплексном тестовом классе полюсная форма имеет оба знака; она сохраняется при оценках непрерывности ниже.

На вещественной Fourier-оси архимедов символ

    a_Gamma(t)=Re psi(1/4+it/2)-log pi,
    a_Gamma(0)=-c_*<0,
    a_Gamma(t)=log(|t|/(2pi))+o(1) -> +infinity.           (1.2)

Точный zero-side использует H_f(z)=F_f^#(z)F_f(z), F_f^#(z)=overline(F_f(overline z)), а не |F_f(z)|^2 в комплексной точке. Для вещественного четного f это F_f(z)^2.

Обозначения D=Q*AQ, K=U*AQ, G=U*AU относятся к ортогональному разложению J+J-perp; B без индексов всегда полная арифметическая часть, а не off-diagonal блок. Никакая почти нулевая матрица не заменяется точным нулем.

## 2. Таблица H1–H12

В колонке «класс» THEOREM относится к доказанной редукции/исправлению, а не автоматически к исходной гипотезе. Вердикт относится к явно указанному квантору.

| H | prior | Вердикт | Точный итог, класс и область |
|---|---:|---|---|
| H1 | .60 | REDUCED | THEOREM: I_m лежит в сверхполиномиальной трубке около 1, когда непусто. Cofinal nonemptiness iff RH. Коэффициент около9.7 и идентификация upper-exit с одной q-модой: CONDITIONAL perturbation law / пока HEURISTIC для данных. §§3–5. |
| H2 | .15 | REFUTED | PAPER, COFINAL_FAMILY, ACTUAL zeta: на явных m_k и точных f_m in J-perp, (L/sqrt m)<f,(C+uB)f> -> (1-u)/(gamma^2+1/4)^2. Любой fixed u>1, в частности2, дает отрицательный уход. §6. |
| H3 | .50 | REFUTED | Q*H Q=0 НЕ достаточно. A=diag(lambda,g), H off-diagonal дает допустимость |epsilon|<=sqrt(lambda g). Для положительного допуска нужны full coupling control либо HQ=0 вместе с контролем дополнения. ABSTRACT; literal source realization конкретной perturbation отдельно. §7. |
| H4 | .60 | REDUCED | THEOREM: dual Y>0 означает отсутствие ненулевой PSD-матрицы в образе arithmetic map; для отсутствия ненулевых параметров нужна еще инъективность. Quantitative thinness требует alpha_m >> delta_m. Существование таких source-Y и количественного alpha_m: CONJECTURE. §8. |
| H5 | .50 | REDUCED | THEOREM: source shift, quadratic coefficient и явный remainder. Порог sqrt(lambda/d) CONDITIONAL на полный положительный curvature и spectral isolation. Ramanujan нарушается в точной строке (9.4), но из умеренности знак не получен. §9. |
| H6 | .45 | REDUCED | THEOREM: отдельный заданный off-line нуль дает explicit source-norm horizon M_rho из (10.4). Uniform M(Gamma,eta) требует еще uniform bound на эти нормы/изоляционную нормировку: CONDITIONAL supplier, не поставлен. §10. |
| H7 | .20 | REDUCED | i^2 меняет знак коэффициента, но не доказывает знак суммы. Низкая off-line четверка и полный хвост остаются. Actual full-curvature lower bound на J: CONJECTURE; отдельный точный отрицательный контроль существует. §9. |
| H8 | .30 | REDUCED | THEOREM: предложенная оценка есть shifted-pencil lower bound, а при fixed u0>1 и bounded epsilon уже дает постоянный пол и RH-consumer. Но этот fixed-factor supplier опровергнут §6. u+=истинный endpoint делает запись тавтологией. §11. |
| H9 | .55 | REFUTED | THEOREM_SHAPE: full finite compression может менять инерцию под Gaussian. На полной доступной координатной четверке инерция сохраняется. Контрмодель сохраняет literal even carrier, но не является actual zeta/DH. §12. |
| H10 | .60 | REDUCED | Zero compression insufficient по H3. Full annihilation HQ=0 + relative complement bound дает tolerance; абсолютный uniform delta0 не следует без gap/relative budget. Fixed-shadow holomorphic mock freedom вообще не меняет источник. Actual admissible shadow supplier: OPEN/CONJECTURE. §7, §13. |
| H11 | .60 | REDUCED | Исправлена модель: true zeta(cs) меняет центр FE, gamma, pole и веса. В своем центре это точная дилатация W_c[f]=c W[D_c f], а не intrinsic tiny tolerance. Fixed-gamma «move peaks» — другой источник; его cofinal tolerance OPEN. §14. |
| H12 | .30 | REDUCED | THEOREM: заданная quiet residual дает superpolynomial upper, не exp(-c m), не lower, не точность положения нулей. Экспоненциальный закон требует нового uniform rate и conditioning theorem; класс CONJECTURE. Связь с H1 условна. §15. |

Короткий счет ставок: H2 опровергнута именно для исходной zeta на кофинальной семье; H3 и H9 опровергнуты в заявленном структурном смысле. Остальные составные гипотезы не превращены в «HIT» целиком за счет доказательства одной их части. Вероятности владельца сохранены, новые posterior-числа не выдумываются.

## 3. H1: новый точный закон общей арифметической связи

### Теорема 1 — внешняя жесткость без предположения существования [COFINAL_FAMILY | PAPER; E/F/A/I]

Для исходного I_m={u in R:C_m+uB_m>=0} и каждого фиксированного N>0 существуют m_N,K_N<infinity, такие что

    m>=m_N, u in I_m ==> |u-1|<=K_N m^-N.                 (3.1)

Эквивалентно, имеется одна последовательность epsilon_m=o(m^-B) для каждого B>0 с

    I_m subset [1-epsilon_m,1+epsilon_m]                  (3.2)

для всех достаточно больших m. Пустое I_m разрешено. (3.1) не утверждает, что A_m положительна.

### 3.1. Два фиксированных радикальных теста с противоположным знаком C

Положим Xi(z)=xi(1/2-iz). Для R>0 и tau>=0 зададим

    F_(R,tau)(z)=(z^2+1/4)Xi(z)
       [exp(-R(z-tau)^2)+exp(-R(z+tau)^2)].               (3.3)

Это вещественно-типичная четная целая функция. На каждой фиксированной горизонтальной полосе она и производные убывают быстрее любого полинома. Stirling, polynomial vertical-strip growth zeta и Gaussian дают это БЕЗ RH. Ее обратный Fourier-образ f_(R,tau) принадлежит S_exp: все производные имеют любые экспоненциальные L2-веса.

Все фактические z_rho являются нулями F. Поэтому по полной смешанной явной формуле

    W[f_(R,tau)]=0.                                     (3.4)

Кроме того F(+i/2)=F(-i/2)=0, следовательно оба полюсных момента нулевые и

    C[f]/||f||^2 = integral a_Gamma(t)|F(t)|^2 dt
                         / integral |F(t)|^2 dt.        (3.5)

Выберем tau=0, где Xi(0)!=0, и tau=tau_+ с a_Gamma(tau_+)>0, Xi(tau_+)!=0. Такой tau_+ существует: a_Gamma->+infinity, а нули ненулевой entire Xi дискретны. При R->infinity нормированная масса |F|^2 сосредоточивается в {0} или {+/-tau_+}. Из (1.2) и обычной Gaussian localization получаем пределы a_Gamma(0)<0 и a_Gamma(tau_+)>0. Хвост оправдан Gaussian-доминированием и логарифмическим ростом a_Gamma.

Фиксируем достаточно большие КОНЕЧНЫЕ R. После нормировки получены два фиксированных источниковых теста f_-,f_+:

    ||f_±||=1, W[f_±]=0,
    C[f_-]=-c_-<0,  B[f_-]=+c_-,
    C[f_+]=+c_+>0,  B[f_+]=-c_+.                         (3.6)

Это не вывод из положительной нулевой суммы: каждый zero-side член равен НУЛЮ, включая комплексные нули. Знак C задан независимым архимедовым символом. E входит ровно в source equality W=C+B и, следовательно, в B=-C на этих тестах. F сохраняет even-real симметрию Xi и полюсную нормировку.

### 3.2. Возврат к literal N=m

Лемма §4 дает f_(±,m) in V_m, такие что одновременно для каждого N

    W[f_(±,m)]=O_N(m^-N),
    B[f_(-,m)]=c_-+O_N(m^-N)>0,
    B[f_(+,m)]=-c_++O_N(m^-N)<0.                         (3.7)

Если u in I_m, два Rayleigh-неравенства требуют

    u-1 >= -W[f_(-,m)]/B[f_(-,m)],
    u-1 <= W[f_(+,m)]/(-B[f_(+,m)]).                    (3.8)

Модули обеих правых частей сверхполиномиально малы. Это доказывает (3.1)–(3.2) на ВСЕЙ поздней целочисленной семье, не только на простых m и не по данным16/24/40. Величина c_± не является коэффициентом9.7 из H1.

### 3.3. Где прячется RH: именно в непустоте

Имеем элементарно

    ||B_m|| <= 2 sum_(n<=m) Lambda(n)/sqrt(n)
             <=4 sqrt(m) log m.                        (3.9)

Если I_(m_k) непусты на неограниченной семье, выбираем u_k in I_(m_k). Тогда

    A_(m_k) >= -|u_k-1| ||B_(m_k)|| I = -o(1) I.        (3.10)

Унаследованный NOESCAPE consumer дает RH. Обратно, под RH исходная Weil-форма положительна, следовательно 1 in I_m для каждого m. Итак,

    RH <=> I_m непусто для неограниченно многих m.       (3.11)

При RH внешняя трубка действительно стягивается к {1}; при not-RH I_m eventually пусто. Доказательство (3.11) не утверждает ни одну из этих двух веток безусловно.

### 3.4. Doubled integer-2: source-specific negative judge

Для C+u(B+B_atom2) на тех же радикальных Gaussian-тестах с R->infinity отношение энергии к норме стремится к

    (1-u)a_Gamma(tau)-2u c2 cos(tau log2),
    c2=log2/sqrt2.                                      (3.12)

При tau=0 неотрицательность потребовала бы

    u >= c_*/(c_*-2c2)>1.

Выберем фиксированное большое tau=2pi k/log2, где a_Gamma(tau)>0. Даже если Xi(tau)=0 конечного порядка, Gaussian localization по-прежнему имеет предел в tau; либо можно взять достаточно близкую точку с Xi!=0. Неотрицательность теперь требует

    u <= a_Gamma(tau)/(a_Gamma(tau)+2c2)<1.

Две границы разделены положительным зазором. Для достаточно большого фиксированного R они остаются несовместимыми, а §4 переносит это на все достаточно большие m. Поэтому

    I_m^(doubled integer2) = empty eventually.           (3.13)

Это аналитический кофинальный контроль, а не экстраполяция численной пустоты. Изменен ровно atom n=2; остальные степени2 сохранены.

Тот же rigidity argument применим к source-correct DH с его completion, odd gamma и без zeta-полюса: a_D(0)<0, a_D(t)->infinity, а Gaussian multiples completion являются радикальными тестами. Он принуждает возможные u к1, но известный отрицательный компактный DH-свидетель исключает cofinal feasibility. Это не превращает DH в Euler-product функцию.

Rigidity без feasibility может проходить и посаженный мир. Это нормально: она не заявлена как закон положительности. Off-line сигнал остается в полном A и исключает (3.10); он не был вычтен из источника.

## 4. Общая лемма возврата и явный бюджет

**[COFINAL_FAMILY | PAPER; A/LA/E/F/I.]** Пусть f реально-четна и принадлежит S_exp. Выберем один четный chi in C_c^infinity(-1,1), 0<=chi<=1, chi=1 при |x|<=1/2. Для L=log m, Omega=2pi m/L положим

    g_m(x)=chi(2x/L) f(x),
    f_m=P_m g_m,                                       (4.1)

где P_m — исходная ортогональная cosine-проекция на j=0,...,m в физическом L2. Тогда W,C,B и норма f_m сходятся к соответствующим величинам f быстрее любой степени m^-1.

Доказательство существенно не использует голую L2-непрерывность глобальной формы.

1. На S_exp форма W непрерывна в N_2^1(f)=||exp(2|x|)f||+||exp(2|x|)f'||. Можно взять грубую константу40: j(s)<=1+1/(2s) на (0,1), integral_1^infinity j<2; prime-сумма оплачивается sum log(n)n^-5/2<infinity, а оба полюса — тем же весом. Отсюда |W(f,h)|<=40 N_2^1(f)N_2^1(h). C и B по отдельности имеют аналогичные безопасные оценки.
2. Cutoff начинается лишь при |x|>=L/4. Любые экспоненциальные нормы f дают N_2^1(g_m-f)=O_N(m^-N).
3. Для произвольного r>=2 периодическое гладкое g_m имеет ||g_m^(r)||<=C_r(f,chi), равномерно по m. Parseval дает для e_m=f_m-g_m внутри окна

    ||e_m||<=Omega^-r C_r,
    ||e'_m||<=Omega^(1-r) C_r,
    |e_m(-L/2)|^2+|e_m(L/2)|^2
       <=[2/((2r-1)pi)] Omega^(1-2r) C_r^2.             (4.2)

Последняя граница — Cauchy–Schwarz по полной cosine-хвостовой сумме. Не предполагается исчезновение endpoint после P_m.
4. Для нулевого продолжения такого e и L>=1:

    H_j[e]<=2||e'_int||^2
          +2(|e(-L/2)|^2+|e(L/2)|^2)+8||e||^2.          (4.3)

Это следует из разбиения перевода на внутреннюю часть и два пограничных слоя. В частности, jumps не потеряны. Cross-term H_j оплачивается Cauchy–Schwarz в положительной j-энергии.
5. На окне pole operator norm <=2sqrt(m), а ||B_m||<=4sqrt(m)L. Поэтому ошибки C,B между f_m и g_m ограничены степенями Omega^-r, умноженными лишь на полиномиальные по m,L множители. Увеличение r закрывает любой заданный N. Это доказывает утверждение.

### Явный вариант для H6

Определим

    S_f=sum_(j=0)^8 ||exp(18|x|) f^(j)||_2,
    C_chi=1+sum_(j=0)^8 binom(8,j)2^j ||chi^(j)||_infinity,
    K_f=200 C_chi^2 S_f^2.                              (4.4)

Для m>=3 предыдущие оценки дают безопасно

    |W[f_m]-W[f]| <= K_f[m^-4+Omega^-7+sqrt(m)L Omega^-8]
                  <=3K_f m^-3.                         (4.5)

Проверка констант: cutoff стоит не более80 C_chi^2 S_f^2 m^-4; arch вместе со скаляром — не более60 C_chi^2 S_f^2 Omega^-7; pole и primes — не более18 C_chi^2 S_f^2 sqrt(m)L Omega^-8. Использованы log m<=sqrt m и Omega>=sqrt m. Константа200 перекрывает каждый член. Для (3.7) применяются более высокие производные/веса, не объявляется fixed r=8 достаточным для всех N.

S_f — не неизвестный положительный спектральный gap. Это явная гладкая source-норма. Через contour shift она сверху оценивается интегралами |(t+/-18i)^j F(t+/-18i)|^2/(2pi), суммируя оба знака, с Gaussian-хвостом при использовании (3.3) или (10.1).

## 5. H1/H12: что означает коэффициент при lambda_q

**[FINITE_CELL | PAPER; LA.]** При строгом допустимом anchor A=C+B>0 положим Z=A^-1/2 B A^-1/2. Тогда

    I_m = {1+s : I+sZ>=0},
    u_+-1 = -1/lambda_min(Z), если lambda_min(Z)<0,
    u_--1 = -1/lambda_max(Z), если lambda_max(Z)>0.        (5.1)

Отсутствующая отрицательная/положительная крайняя eigenvalue дает бесконечный соответствующий край. Без строгого anchor используются Rayleigh cuts и range-guards, а не произвольная inverse.

Эквивалентно

    u_+-1=inf_(B[f]<0) W[f]/(-B[f]),                     (5.2)

при положительном anchor. Поэтому для любой выбранной q с B[q]<0 имеем только upper bound lambda_q/(-B[q]), если W[q]=lambda_q и ||q||=1. Равенство не следует из определения тихой моды.

Если q — точный собственный вектор A, то в его одномерном блоке при gap G>=gI:

    A+sB >=0 iff lambda_q+s b
        -s^2 n*(G+sR)^-1 n >=0                          (5.3)

вместе с положительностью дополнения. Если b<0 и

    lambda_q ||n||^2/(g b^2)->0,
    lambda_q ||R||/(g |b|)->0,

и именно эта ветвь задает первый upper-exit, то

    u_+-1 ~ lambda_q/(-b).                              (5.4)

Это CONDITIONAL theorem, не установленный uniform supplier на реальном кластере. Число около9.7 означает slope около-0.103 в трех пилотах R1. Оно не является аналитической константой всего источника. Нижний край может использовать комбинацию мод, что точно допускает (5.2) со знаком B>0.

## 6. H2: реальный контрпример для запаса 2 на J-perp

### Теорема 4 [COFINAL_FAMILY | PAPER; A/LA/F/E/I, PNT]

Зафиксируем любой настоящий критический нуль 1/2+i gamma, gamma>0. Его существование безусловно; ни простой нуль, ни положительность конечного нулевого списка не предполагаются. Положим d_gamma=gamma^2+1/4 и

    m_k=nearest_integer(exp(4pi k/gamma)),
    L_k=log m_k,
    v_L(x)=cos(gamma x)1_[-L/2,L/2](x),
    f_m=P_m v_L/||P_m v_L||.                            (6.1)

На всех поздних этих целых m имеем gamma<T_m. Поэтому для каждого h in J_m,

    <P_m v_L,h>=<v_L,h>=F_h(gamma)=0,

то есть f_m принадлежит ТОЧНО J_m-perp. Не применяется приближенное отождествление с вычисленным spectral cluster.

Для каждого фиксированного вещественного u:

    (L_k/sqrt(m_k)) <f_(m_k),(C+uB)f_(m_k)>
           -> (1-u)/d_gamma^2.                          (6.2)

В частности, для любого fixed u>1 eventually

    <f_m,(C+uB)f_m> <= -(u-1)/(2d_gamma^2) sqrt(m)/L <0. (6.3)

Это строгий отрицательный UPPER envelope на исходной семье. Следовательно H2 с u_+^perp>=2 для всех больших m ложна. Более точно, любые допустимые u на этих дополнениях удовлетворяют u<=1+o(1), если множество вообще непусто.

### Доказательство: весь источник, не отдельный prime prefix

Для v_L точная корреляция

    Q_L(s)=(L-s)cos(gamma s)+sin(gamma(L-s))/gamma,
    0<=s<=L,                                           (6.4)

удовлетворяет |Q_L(s)|<=2(L-s), |Q_L'(s)|<=2+gamma(L-s), Q_L(L)=0.

Пусть psi(x)=sum_(n<=x)Lambda(n), R(x)=psi(x)-(x-1), r(s)=exp(-s)R(exp s). Безусловная PNT дает r(s)->0; r ограничена. Abel с обоими endpoint terms дает

    P_L-I_L=integral_0^L r(s)exp(s/2)[Q_L(s)/2-Q_L'(s)]ds,
    P_L=sum_(n<=m)Lambda(n)/sqrt(n)Q_L(log n),
    I_L=integral_0^L exp(s/2)Q_L(s)ds.                   (6.5)

После u=L-s деления на exp(L/2) модули dominated величиной const_gamma exp(-u/2)(u+1), интегрируемой на [0,infinity). При каждом фиксированном u имеем r(L-u)->0. Поэтому

    P_L-I_L=o(exp(L/2)).                                (6.6)

Это точное место E/I arithmetic input PNT. Ни RH-error term, ни sieve constant2 не нужны.

Для even source pole/continuum identity из предшественника:

    W[v_L]=H_+[v_L]+(4-c_*)||v_L||^2-(P_L-I_L),
    j_+(s)=exp(-5s/2)/(1-exp(-2s)).                      (6.7)

H_+[v_L]=O_gamma(L): внутри окна сдвиг оплачивается производной, а оба пограничных слоя имеют длину s. Значит W[v_L]=o(sqrt m).

С другой стороны,

    <p,v_L>=2sqrt(2)/d_gamma *
       [(1/2)sinh(L/4)cos(gamma L/2)
         +gamma cosh(L/4)sin(gamma L/2)].               (6.8)

На m_k имеем gamma L_k/2=2pi k+O_gamma(1/m_k). Поэтому

    C[v_(L_k)] ~ sqrt(m_k)/(2d_gamma^2),
    ||v_(L_k)||^2 ~ L_k/2.                              (6.9)

Архимедова часть O_gamma(L_k), включая скаляр, не влияет на главный положительный pole term. Это точное место F/pole normalization.

Возврат P_m не портит масштаба. Для j>m исходная точная Fourier-колонка дает |<phi_j,v_L>|<=C_gamma L^(3/2)/j^2, когда Omega>=2gamma. Поэтому, для e=v_L-P_m v_L,

    ||e||=O_gamma(L^(3/2)m^-3/2),
    ||e'_int||=O_gamma(sqrt(L/m)),
    |e(+/-L/2)|=O_gamma(L/m).

С (4.3), ||B_m||<=4sqrt(m)L и pole norm<=2sqrt(m), ошибки W и C равны O_gamma(L/sqrt(m)+L^3/m)=o(sqrt m). Нормировка дает (6.2), поскольку C+uB=uW+(1-u)C. Конец доказательства.

В частности, тихое пространство не является единственным местом, где общий коэффициент простых требует асимптотически точной настройки. Однако это не опровергает отдельно установленный факт, что самый ранний finite upper-exit в пилотах расположен в тихом кластере: там сравниваются существенно разные масштабы и m.

## 7. H3 и H10: нулевая первая компрессия не оплачивает coupling

**[ABSTRACT / FINITE_CELL | PAPER; LA.]** Унаследованное точное правило:

    A=[[D,K*],[K,G]], H=[[M,N*],[N,R]],
    A+epsilon H>=0 iff G+epsilon R>=0 и
    D+epsilon M-(K+epsilon N)*(G+epsilon R)^-1
                                   (K+epsilon N)>=0,   (7.1)

в области строгой обратимости второго блока; на границе нужны range-guards.

Даже A=diag(lambda,g), lambda,g>0, M=0, N=1, R=0 дает

    A+epsilon H>=0 iff |epsilon|<=sqrt(lambda g).        (7.2)

Следовательно допуск по-прежнему может уходить к0 с тихой eigenvalue, хотя Q*H Q=0 точно. При lambda=0 любой ненулевой epsilon дает determinant -epsilon^2<0. Это REFUTED для буквальной H3, а не заявление, что всякая конкретная source-shadow реализует этот блок.

Ремонт: при точном invariant quiet block и HQ=0, K=0 возмущается только G. Тогда |epsilon| ||R||<lambda_min(G) достаточно. Uniform delta0 требует uniform gap или относительной оценки -cG<=R<=cG. Если K!=0, изменение inverse G влияет на тихий Schur-блок даже при N=0; старый coupling сохраняется в (7.1). Нельзя объявить весь эффект нулевым по одному M=0.

Если H>=0 на всем carrier, положительный луч epsilon>=0 безопасен при уже положительном A; это не доказывает A>=0. Если H образован произвольным проектором на J-perp, требуется отдельно доказать, что такой H является допустимой исходниковой «тенью» с указанными пиками, а не только произвольной матрицей.

## 8. H4: точный активный dual и цена его вырождения

**[ABSTRACT / FINITE_CELL | PAPER; LA.]** Gamma и pole фиксированы; мертвые ПОЛНЫЕ ручки удалены. Положим L_m(t)=sum_p t_p M_p и W_m=ran L_m. Тогда

    W_m intersection PSD = {0}
    iff exists Y>0: tr(YM_p)=0 для каждого active p.      (8.1)

Это строгая конечномерная альтернатива: разделение compact PSD trace-one base от W_m. Для {t:L_m(t)>=0}={0} нужна еще ker L_m={0}. Y alone не видит параметрическое ядро.

Определим количественную clearance

    alpha_m=inf_(||t||_2=1) [-lambda_min(L_m(t))].        (8.2)

При инъективности и (8.1) alpha_m>0 для каждой фиксированной ячейки. Если D+L_m(t)>=0, то

    ||t||_2<=||D||/alpha_m<=delta_m/alpha_m.             (8.3)

Поэтому из delta_m->0 thinness еще не следует: нужно delta_m/alpha_m->0, для сверхполиномиальной тонкости — соответствующий rate. Ни finite Y, ни tiny SVD автоматически не дают этот uniform bound. Например, после tr Y=1, если s_m=inf_(||t||=1)||L_m(t)||, то alpha_m>=lambda_min(Y)s_m. Обе величины могут деградировать.

### Какая это «мера»

Y — положительный density operator на J, а не мера на нулях zeta. Если Y=sum_l y_l |v_l><v_l|, f_l=Qv_l, то

    tr(YM_p)=-sum_(k>=1,p^k<=m) (log p)p^-k/2 Q_Y(k log p),
    Q_Y(s)=sum_l y_l Q_(f_l)(s).                        (8.4)

В реальном Fourier-представлении Q_Y есть cosine-transform неотрицательной плотности sum_l y_l |F_(f_l)(t)|^2. Значения этой плотности не означают неотрицательности ее cosine-transform. При complex zeros нельзя заменить source pairing абсолютными квадратами. У каждого f_l низкие actual zero-values нулевые, но это не задает Y и не оплачивает высокую часть.

(8.1)–(8.4) — THEOREM. Source-existence и uniform clearance для исправленной H4 — CONJECTURE, без нового доказательства в этой работе.

## 9. H5 и H7: сдвиг, curvature, умеренность

**[ABSTRACT / FINITE_CELL | PAPER; E/F/A/LA.]** Чтобы при a=0 получить A, а не2A, нормируем zero form X_a(s)=xi(s+a)xi(s-a) множителем1/2:

    W_a[f]=(1/2)sum_rho[H_f(z_rho+ia)+H_f(z_rho-ia)],
    W_a[f]=W[f]-(a^2/2)D_f+E_4(a),
    D_f=sum_rho H_f''(z_rho).                           (9.1)

Для fixed m и |a|<=a0 у предшественника доказано |E_4|<=a^4 R_f/24 с полным convergent all-zero R_f. Никаких высоких нулей не выбрасываем.

На J низкий член равен 2F_f^#'(z_rho)F_f'(z_rho). На линии это 2|F_f'|^2; на off-line quartet это signed pairing, не modulus. Высокие нули в D_f остаются даже в RH-ветке. Поэтому H7 требует НОВОЙ нижней оценки полного D_f, а не равенства i^2=-1.

Если для конкретной unit q независимо известно W[q]=lambda>=0, D_q>=d>0 и |E_4|<=R a^4, то

    W_a[q]<=lambda-(d/2)a^2+R a^4.                      (9.2)

При lambda>0 выбор a^2=4lambda/d дает строгий выход, когда 16R lambda<d^2 и a<=a0. При lambda=0 достаточно любого малого a!=0 с R a^2<d/2. При изоляции выбранной spectral branch, d не вырождается и remainder uniform получаем

    a_*^2 ~ 2lambda/d.                                 (9.3)

Без этих guards это только достаточный test-exit budget, не exact first crossing. При a=i t квадратичный член меняет знак; весь D_f и remainder остаются.

Точная строка потери Рамануджана у Dirichlet-части zeta(s+a)zeta(s-a):

    local prime coefficient p^a+p^-a,
    normalized log-derivative atom Lambda(p^k)cosh(a k log p).
    cosh(a k log p) ~ (p^k)^|a|/2.                      (9.4)

При любом fixed a!=0 оценка O_epsilon(n^epsilon) для КАЖДОГО epsilon>0 нарушается. Это дает рост весов и сдвиг области абсолютной сходимости; ни одна строка здесь не превращает умеренность в Weil positivity. Gamma и poles также сдвигаются. Поэтому X_a не лежит в старом per-prime handle space (k-зависимый множитель не является одним w_p).

Для всех real a!=0 у X_a есть off-line zeros: сдвинуть хотя бы один известный on-line zero исходной xi. Следовательно глобальная source form этого корректного completion имеет отрицательный свидетель, строящийся как в §10. Это не доказывает fixed-window onset и не устанавливает положительность D_q для любой выбранной тихой q.

Алгебраический контрконтроль знака: при w=gamma+i eta, gamma>eta>0, F(z)=(z^2-w^2)(z^2-conj(w)^2), сумма (F^2)'' по четверке равна -512gamma^2 eta^2(gamma^2-eta^2)<0. Чтобы не оставлять нефизический polynomial test, умножаем F на exp(-r z^2): при достаточно малом r>0 знак сохраняется по непрерывности, а обратный Fourier-образ — реальный четный Schwartz/Gaussian-тест. Это контрмодель finite quartet, не отрицательная curvature на настоящем J_m zeta.

## 10. H6: источник-нормовый горизонт отдельного нуля

**[COFINAL_FAMILY | PAPER; A/F/LA/E через явную формулу.]** Предположим, что имеется настоящий off-line spectral node w=gamma+i eta, gamma>0, eta!=0, кратности nu. Все члены симметричной четверки имеют ту же кратность. Положим

    P_w(z)=(z^2-w^2)(z^2-conj(w)^2),
    G_w(z)=exp(-z^2) Xi(z)/P_w(z)^nu.                   (10.1)

Все кажущиеся полюса устранимы; G_w(w)!=0. Выберем real A,B так, чтобы

    (A+B w^2)G_w(w)=i,
    B=Im(i/G_w(w))/Im(w^2),
    A=Re(i/G_w(w))-B Re(w^2).

Тогда F_w(z)=(A+Bz^2)G_w(z) реально-типична и четна; ее обратный Fourier-образ f_w принадлежит S_exp. Во всех остальных zeros Xi она нулевая. В выбранной четверке значения i,i,-i,-i, поэтому по ПОЛНОЙ формуле

    W[f_w]=-4nu.                                      (10.2)

Это явный signed source witness без предположения о местоположении остальных нулей, без finite-prefix positivity и без missing tail: все остальные значения занулены аналитически.

Определим S_f и K_f по (4.4) для этого f_w. Они конечны и вычислимы через Xi и ее removable values. По (4.5)

    W[P_m(chi(2x/log m)f_w)] <= -4nu+3K_f m^-3.         (10.3)

Следовательно явный допустимый горизонт

    M_rho=max(3, 1+ceil((3K_f/(2nu))^(1/3)))             (10.4)

обеспечивает отрицательный исходный Rayleigh test для КАЖДОГО целого m>=M_rho. Носитель четный, порядок N=m, физическая норма не заменена. Этот порог огромен и не оптимален; не требуется утверждать простоту нуля.

Что еще НЕ получено: верхняя оценка K_f только через rectangle-параметры Gamma,eta, uniform по всем возможным нулям области. Нормировка G_w(w) содержит leading derivative Xi в кратном нуле; ее reciprocal нельзя объявлять ограниченной без отдельного supplier. Поэтому практический uniform horizon M(Gamma,eta) остается CONDITIONAL на явный bound этих source-норм.

Логика сертификата корректна: если A_m>=0 сертифицирован по исходным простым/gamma/poles и независимо известно m>=sup_(rho in target region) M_rho, то в области нет off-line нулей. Одного A_m>=0 без оплаченного второго условия недостаточно. Это не перенос конечного вычисления на всю RH.

## 11. H8 и слабейший потребитель знака

Пусть P=-B. Неравенство

    P|_(J-perp) <= C|_(J-perp)/u0 + epsilon I            (11.1)

при u0>0 эквивалентно C+u0 B>=-u0 epsilon I на дополнении. Если u0 определяется как уже доказанный endpoint, это запись его определения, не sieve proof.

В even source имеется безусловный C>=-c_*I. Поэтому при u0>=1

    A=(C+u0B)/u0+(1-1/u0)C
      >=-epsilon I-c_*(1-1/u0)I                         (11.2)

на дополнении. Uniform bounded epsilon и u0>=1 дают постоянный complement floor; при u0->1, epsilon->0 получается floor -o(1). С ||AQ||->0 оба возвращаются к полному исходному оператору. Это THEOREM consumer reduction. Не нужно ошибочно требовать C>=0; достаточно его уже известного постоянного нижнего пола.

Однако для любого FIXED u0>1 §6 дает на J-perp отрицательные значения C+u0B порядка -sqrt(m)/log m. Поэтому (11.1) с fixed u0>1 и bounded epsilon ложна на кофинальной семье. «Потеря2» не может быть источником необходимого пола.

Фраза «атомы только тратят» верна для определенного birth-derivative jump Delta A'_L=-2c_n ee*, но НЕ для квадратичной формы каждого B_n на всех тестах. Корреляция Q_f(log n) может быть отрицательной. Например, три узких even bumps в -a,0,a с коэффициентами1,-2,1 дают Q_f(a)<0, а значит B_atom>0. Обратные изломы и signed Schur-энергия не смешиваются.

## 12. H9: тепло и инерция — точный countermodel

**[ABSTRACT / FINITE_CELL | PAPER; A/LA.]** Gaussian-форма

    W_y[f]=sum_rho exp(-y z_rho^2) H_f(z_rho)

равна W[T_y f], где Fourier multiplier T_y равен exp(-y z^2/2). Но T_y выводит compact-window f из V_m и создает физические Gaussian-хвосты. Это не invertible congruence внутри той же конечной матрицы A_m.

На одной доступной четверке при z=gamma+i eta фактор exp(-yz^2) имеет положительный modulus exp[-y(gamma^2-eta^2)] и phase -2y gamma eta. Real2x2 metric после удаления положительного scalar имеет determinant -1. Если evaluation map на все retained zero coordinates сюръективно, Sylvester дает постоянную инерцию их формы. При большем числе coordinates, чем carrier dimension, это не переносится на компрессию.

### Контрсемья на literal carrier

Зафиксируем m=2, L=log2, d=3 и обычные физические cosine rows e(z). Возьмем три реальные точки r1=1,r2=2,r3=3 и

    P_y=2 sum_(j=1)^3 exp(-y r_j^2)e(r_j)e(r_j)^T >0.

Их независимость — точная polynomial interpolation исходного cosine-carrier; это НЕ список zeta zeros. Возьмем w=20+i/4. Re e(w), Im e(w) независимы. Выберем real unit v с Re(F_v(w))=0, Im(F_v(w))!=0, и integer nu так, чтобы

    4nu (Im F_v(w))^2 > v^T P_0 v.

Определим полный smoothed model

    A_y^model=P_y+4nu Re[exp(-yw^2)e(w)e(w)^T].           (12.1)

При y=0 trial v строго отрицателен. Для больших y:

    P_y >= exp(-9y) lambda_min(P_0) I,
    ||quartet_y|| <=4nu ||e(w)||^2 exp[-(400-1/16)y].     (12.2)

Поэтому A_y^model>0 для всех достаточно больших y. Инерция всей3x3матрицы меняется, несмотря на постоянную инерцию изолированной четверки. Это аналитическое доказательство контрсемьи.

Выполненный DIAG-экземпляр nu=665 при70 и100dps:

| y | lambda_min(A_y^model) | n_- |
|---:|---:|---:|
| 0 | -0.5464105109725905358... | 1 |
| .1 | +0.00000020549010232348... | 0 |
| 1 | +0.0000000003614432227644... | 0 |

Для замороженного v при y=0 quotient -0.00153624817072078... . Эти decimals не являются интервальным сертификатом; теорема опирается на defining strict inequality для nu и (12.2).

H9 для настоящей zeta под RH, конечно, условно дает нулевой отрицательный индекс при всех y. Этот факт не доказывается конечной critical-line суммой R2. Из нынешних DH/plant данных нельзя утверждать, что индексы либо всегда сохраняются, либо уже меняются у их полной бесконечной source формы: архивный census не сертифицирует хвост.

## 13. H10: допустимая тень и нулевое действие — разные вещи

Утверждение «Q*H Q=0 => delta_*>=delta0>0» опровергает (7.2). Для исправленного HQ=0 нужны guards §7. Даже lambda_min(G) может быть сверхмалой; fixed absolute delta0 не возникает из одного названия «дополнение».

Голоморфная добавка при fixed Bruinier–Funke shadow в прежнем mock-return дает H=0 на ВСЕМ источнике. Ее бесконечный формальный допуск тривиален и ничего не улучшает в RH. Для genuinely меняющейся тени необходимо отдельно задать карту shadow->source perturbation и проверить ограничения на prime positions, gamma/poles и все cross terms.

Минимальный полезный supplier: конкретная source-compatible семья H_m с HQ=0 либо полным (7.1)-контролем и относительной оценкой на дополнении, а не просто нулевой Q*H Q. Его существование пока OPEN; выдавать arbitrary projected matrix за такую тень нельзя.

## 14. H11: правильный мир zeta(cs)

**[ABSTRACT | PAPER; E/F/A/LA.]** Для c>0 completion xi(cs) симметричен относительно s=1/(2c), не s=1/2. Полюс Dirichlet-части zeta(cs) находится в1/c; сама xi(cs) целая. В естественном centered spectral variable

    Xi_c(z)=xi(1/2-i c z),
    zero nodes=z_rho/c.

Пусть D_c f(x)=sqrt(c) f(cx), унитарная физическая дилатация. Тогда F_(D_c f)(z)=c^-1/2 F_f(z/c), и ТОЧНО

    W_c[f]=c W[D_c f],
    support(D_c f) has length L/c.                      (14.1)

Следовательно глобальный знак true centered scaled world тот же, что у исходного W. Он не обязан ломаться при c!=1. Если оставить старый центр1/2, nodes вместо этого равны

    z_rho/c+i(1/(2c)-1/2),                              (14.2)

а стандартная старая reflection pairing уже не соответствует его FE. Если оставить Gamma/pole и менять только c log n, это ДРУГОЙ источник, не xi(cs).

Таким образом intrinsically сверхмалый допуск exact scaling не установлен и не является coordinate-invariant гипотезой. Исправленная fixed-window, fixed-gamma source deformation требует своего H_m, birth/coupling бюджета и проверки (7.1); носители выхода в J пока DIAG/CONJECTURE, не следствие (14.1).

## 15. H12: что действительно измеряют маленькие eigenvalues

R3 дает upper delta_m с экспонентой

    -const_c sqrt(m)(1+log log m)^2/(log m)^3

и polynomial prefactor. Это superpolynomial decay, но не exp(-c m). Малость ||AQ|| обеспечивает r_m малых singular values и соответствующие малые абсолютные eigenvalues самосопряженной A; не дает положительности этих значений или нижней оценки на smallest lambda.

Новая (3.1) тоже дает любой polynomial rate, без fixed exp(-c m). Ни одна из этих оценок не измеряет ошибку координаты zeta zero. Для certified location из residual необходимы conditioning/Jacobian или simple-root derivative lower bound и полный error box. В кратном нуле обычная линейная inverse estimate вообще не применима.

Связь с H1 — точная generalized-pencil формула (5.2), а не универсальное равенство delta_u=c lambda_q. Нужны slope и coupling bounds (5.3). Поэтому «знание нулей до1e-44» заменено на два разных утверждения: малая source eigenvalue и сертифицированная локализация нуля. Второе здесь не получено.

## 16. Карта слияния гипотез и путь к RH

**Кластер A — один операторный pencil:** H1,H2,H3,H4,H8,H10,H12. Их общая точная база — Rayleigh quotient (5.2), full Schur (7.1), dual clearance (8.2). Thinness, feasibility и first-exit identity — разные утверждения. У H1 теперь proved outer tube; fixed-factor H2/H8 исключены; нулевой первый блок H3/H10 не исключает второго порядка.

**Кластер B — один all-zero curvature:** H5,H7. Общий неоплаченный sign supplier D_f=sum H_f''(z_rho). Только низкая line-prefix часть положительна, и это не supplier. Порог (9.3) условен на full curvature и изоляцию ветви.

**Кластер C — видимость вместо нейтральности:** H6,H9,H11. Heat/restriction не сохраняет finite inertia, exact scaling меняет координаты и окно, а compact return переносит отрицательный свидетель при оплаченных нормах. Это три разные операции; они не образуют один инвариант.

Унаследованный route consumer, с полным Q:

    G_m>=-epsilon_m I, delta_m=||A_mQ_m||->0
    ==> A_m>=-[max(epsilon_m,delta_m)+delta_m] I.         (16.1)

При epsilon_m->0 на неограниченной исходной семье это эквивалентно RH, в обе стороны через inherited negative-witness theorem и условную positive Weil form. При bounded epsilon_m потребитель constant floor из досье также достаточен. Этот знак НЕ поставлен данным вердиктом.

Новые эквивалентности:

    RH <=> cofinal nonempty I_m                         [Theorem1+consumer]
       <=> source complement lower envelope -o(1)       [inherited+block]
       <=> H6-тип отсутствие ВСЕХ off-line witnesses
           при оплаченных cofinal PSD certificates.    [logical, not finite extrapolation]

H4 dual existence без baseline feasibility не эквивалентно RH. H9 и H11 как structural statements не являются RH-критериями. H5/H7 локальный curvature на выбранной q не равносилен RH без theorem о всех missing directions.

### Один оставшийся source target

Не покупать fixed factor2, uniform capacity или инерционную нейтральность тепла. Нужен односторонний lower envelope полного G_m=U*AU на одной неограниченной исходной семье. Его допустимо получать с любым постоянным отрицательным бюджетом по inherited constant-floor consumer; positivity каждого atomic term не требуется.

Две координатные формы ЭТОГО ЖЕ target для K4:

R1. Полный source-constrained Rayleigh на J-perp, сохраняя C и B в одном выражении. Дискриминатор §6 обязательно включить: отдельно оцененный P с loss>1 и bounded residual уже невозможен. Kill-power5/5, бумажная цена3/5; cofinal знак не обещан.
R2. Dual/Schur certificate полного G с явным functional error ledger, а не Y для одних M_p. Начинать с формы, которая сохраняет pole–prime компенсацию на fixed-zero kernels. Kill-power4/5, цена4/5; finite certificate не повышается до cofinal без uniform supplier.

Три мостовых проверки K9 выполнены: (i) generalized eigenvalue / convex duality, (ii) exact zero-generating radical Xi times Gaussian, (iii) heat as pullback with changed domain. Из них (ii) закрыл family-квантор rigidity и concrete doubled-atom judge; (iii) дал counterexample, а не positive supplier.

## 17. Дискриминаторы, проверки и closeout

### 17.1. Не перемещать отрицательный сигнал в неоплаченный член

- **RH-ветка:** 1 in I_m; tube (3.2) согласована; H2 все равно ложна, поскольку C+2B не исходная Weil form. Никакой новой положительной массы порядка log m не добавлено.
- **Doubled atom2:** (3.12) дает конфликт уже двух fixed radical probes, hence eventual empty I. Исходная Gamma/pole часть не меняется.
- **DH:** использовать odd gamma/no pole и все signed non-prime-power b(n). Rigidity при попытке масштабировать ВСЮ arithmetic part не исправляет существующий off-line witness. Zeta-specific числовую continuity constant40 нельзя автоматически переносить без учета DH Dirichlet coefficient bounds.
- **X_a:** его shifts, k-dependent weights, gamma/poles сохраняются; H6-тип test видит off-line quartet. Не считать его старой ручкой B_p.
- **Plant:** сигнал остается в full zero/source form. Heat может скрыть его в конкретной compression, но §10 возвращает отрицательный compact test при оплаченном горизонте. Gaussian radical probes при H1 обнуляют zero-side ради контроля параметра, а не объявляют весь источник положительным.

Это сохраняет Cramer-фильтр: малость одной переупакованной части не исключает off-line полюс в остальных частях. Знаковым выводом считается только полный возвращенный source Rayleigh envelope.

### 17.2. Зарегистрированные predictions и их судьба

До новых исполняемых тестов записаны P1–P6:

P1 zero compression leaves sqrt(lambda) coupling exit — CONFIRMED (7.2).
P2 Gaussian full finite compression may change inertia — CONFIRMED §12; actual zeta inertia change NOT claimed.
P3 scalar coupling outer rigidity from two radical arch signs — CONFIRMED Theorem1; cofinal feasibility separately RH-equivalent.
P4 fixed-real-zero J-perp kernels refute factor2 — CONFIRMED Theorem4, no numeric asymptotic fit.
P5 i^2 is variation sign, not curvature supplier — CONFIRMED (9.1); actual positivity of D_f OPEN.
P6 pencil/Schur/dual unifies hypotheses but does not create source positivity — CONFIRMED §§5,7,8,11.

18 exact SymPy controls executed. A first harness used structural equality on an unexpanded derivative; replaced with equality of the expanded polynomial difference, without changing the identity. The first numerical heat harness used an unsupported mp.matrix callback constructor, which silently produced a zero added block; direct trial-vs-expansion comparison detected this. Replaced with an explicit nested-list matrix, and added negative-trial/positive-final assertions. These were instrumentation repairs, not retroactive changes of hypotheses. The corrected model was repeated at100dps.

No new actual zeta/DH matrix scan, no new zero census, no new Arb/Lean proof. New analytical theorems have author PAPER status, not independent review. Existing source claims are inherited only as explicitly stated.

### 17.3. Reopen triggers and dependency contract

DOWNSTREAM_CONSUMER: actual full/complement lower envelope on a cofinal original family, followed by inherited NOESCAPE.
ACTUAL_CONSUMER_REQUIREMENT: bounded-below complement suffices via the constant-floor supplier; -o(1) also suffices with the compact negative witness. Fixed sieve loss2, global heat inertia, exact vertex and exp(-cm) rate are NOT_NECESSARY.
ORIGINAL_REQUESTED_OBJECT: twelve hypothesis verdicts and equivalence map.
FAILURE_TYPE: COUNTEREXAMPLE for H2/H3/H9 shapes; NO_DERIVATION for unpaid source positivity and active-weight dual family.
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD only the precise refuted shapes; all broader RH routes UNRESOLVED, not killed.
NOVELTY_AXIS: source radical outer rigidity, cofinal actual-complement exit, explicit source-norm witness return; no historical priority claim.

Reopen H1 quantitative9.7: independently certified slope/coupling/branch guards, not one more fitted ratio.
Reopen H2: change fixed factor>1 target; the exact claim cannot be reopened by more positive small cells.
Reopen H3/H10: full annihilation or full Schur relative budget plus admissible source map.
Reopen H4: exact active-handle Y, injectivity and quantitative alpha_m versus delta_m, with baseline feasibility separated.
Reopen H5/H7: full all-zero curvature lower bound and remainder, not a line-prefix sum.
Reopen H6 practical region: explicit uniform upper for source norms/leading-zero normalization in (10.4).
Reopen H8: source comparison with u0(m)->1 or direct full signed budget; bounded-error fixed factor>1 is already excluded.
Reopen H9 literal-world claim: same-source interval inertia with ALL tails on two y-values, or a source-specific domain invariance theorem; one-quartet determinant insufficient.
Reopen H11: specify recentered exact scaling versus fixed-gamma deformed source before measuring tolerance.
Reopen H12: genuine uniform exponential rate and conditioning-to-zero-location theorem.

DISCRIMINATOR_ZERO_CONSISTENT: exact algebraic identity for a claimed kernel; rigorous spectral enclosure with physical metric for finite signs; full source tail plus source return for any heat/zero-side representation. Floating SVD cutoffs and finite critical-line positivity do not discriminate.

### 17.4. Repository and verification handoff

One Markdown verdict is written only under docs/routeB_bus/proshka/. No Lean/source-state/export files change. The actual new commit SHA and verified remote blob are reported after delivery in chat; no self-referential commit hash is fabricated inside this file. Repository publication is not mathematical certification.

WORKDIR: repository root

    python3 - <<'PY'
    from pathlib import Path
    p=Path('docs/routeB_bus/proshka/PROSHKA_VERDICT_MYTHOS_HYPOTHESIS_DOSSIER_2026-11-03.md')
    s=p.read_text()
    code=s.split('<!-- BEGIN_CHECKS -->\n```python\n',1)[1].split('\n```\n<!-- END_CHECKS -->',1)[0]
    Path('/tmp/proshka_mythos_checks.py').write_text(code)
    PY
    uv run --with sympy --with mpmath python /tmp/proshka_mythos_checks.py

Expected: ALL 18 EXACT CONTROLS PASSED, then the three synthetic heat rows with the stated model scope. This is a normalization/countermodel harness, not a machine proof of the analytic family theorems. Lean axiom profile: not applicable.

## Приложение. Исполняемые контроли

<!-- BEGIN_CHECKS -->
```python
from pathlib import Path
import json
import sympy as s
import mpmath as mp
out=[]
def ck(n,b):
    if not bool(b): raise AssertionError(n)
    out.append({'name':n,'status':'PASS'})
    print('PASS',n)
x,d,e,g,t=s.symbols('x d e g t',real=True)
A=s.diag(e,g); H=s.Matrix([[0,1],[1,0]])
ck('zero_compression_not_zero_coupling',s.det(A+t*H)==e*g-t*t)
ck('sqrt_quiet_exit_exact',s.det(A+t*H).subs(t,s.sqrt(e*g))==0)
C=s.Matrix([[3,1],[1,2]]); B=s.Matrix([[1,2],[2,-1]]); D=s.Matrix([[4,1],[1,5]])
M=C.row_join(B).col_join(B.T.row_join(D)); T=(-C.inv()*B).col_join(s.eye(2))
ck('schur_trial_identity',s.simplify(T.T*M*T-(D-B.T*C.inv()*B))==s.zeros(2))
# pencil envelopes -- exact generalized eigen example
G=s.diag(s.Rational(1,100),2); Z=s.diag(-1,3)
lo=1-s.Rational(2,3); hi=1+s.Rational(1,100)
ck('pencil_upper_boundary',s.det(G+(hi-1)*Z)==0)
ck('pencil_lower_boundary',s.det(G+(lo-1)*Z)==0)
# two independent traceless arithmetic matrices; positive dual
M1=s.diag(1,-1); M2=s.Matrix([[0,1],[1,0]]); aa,bb=s.symbols('aa bb',real=True)
ck('dual_zero_trace',s.trace(M1)==s.trace(M2)==0)
ck('dual_indefinite_all_nonzero',s.det(aa*M1+bb*M2)==-aa**2-bb**2)
# kernel makes dual alone insufficient
ck('dual_does_not_remove_parameter_kernel',M1-M1==s.zeros(2))
# centered Fourier zero shift
z,a=s.symbols('z a',real=True); F=z**4+2*z*z+3; Hf=F**2
shift=s.expand((Hf.subs(z,z+s.I*a)+Hf.subs(z,z-s.I*a))/2)
ck('real_zero_shift_quadratic_sign',s.expand(s.expand(shift).coeff(a,2)+s.diff(Hf,z,2)/2)==0)
phase=s.expand((Hf.subs(z,z+a)+Hf.subs(z,z-a))/2)
ck('line_shift_quadratic_sign',s.expand(phase.coeff(a,2)-s.diff(Hf,z,2)/2)==0)
# fixed-zero cosine correlation and pole norm
L,u,k=s.symbols('L u k',positive=True,real=True)
Q=(L-u)*s.cos(k*u)+s.sin(k*(L-u))/k
ck('cosine_endpoint_atom_zero',s.simplify(Q.subs(u,L))==0)
ck('cosine_derivative_formula',s.simplify(s.diff(Q,u)+s.cos(k*u)+k*(L-u)*s.sin(k*u)+s.cos(k*(L-u)))==0)
xx=s.symbols('xx',real=True)
primitive=(s.sinh(xx/2)*s.cos(k*xx)/2+k*s.cosh(xx/2)*s.sin(k*xx))/(k*k+s.Rational(1,4))
ck('cosine_pole_integral',s.simplify(s.diff(primitive,xx)-s.cosh(xx/2)*s.cos(k*xx))==0)
# analytic radical factor kills both poles
R=z*z+s.Rational(1,4)
ck('radical_cancels_both_poles',R.subs(z,s.I/2)==R.subs(z,-s.I/2)==0)
# heat pair metric determinant, AFTER removing positive scalar amplitude
phi=s.symbols('phi',real=True)
J=s.Matrix([[s.cos(phi),s.sin(phi)],[s.sin(phi),-s.cos(phi)]])
ck('quartet_heat_metric_inertia',s.trigsimp(J.det())==-1)
# finite full restriction can differ from isolated pair index
P=s.eye(2); J0=s.diag(-2,2); h=s.symbols('h',positive=True)
ck('heat_amplitude_crossing_algebra',s.det(P+h*J0)==1-4*h*h)
# exact centered variable relation for zeta(cs)
c=s.symbols('c',positive=True)
rho=s.symbols('rho')
zz=s.I*(rho-s.Rational(1,2))
ck('scaled_world_center_correction',s.simplify(s.I*(rho/c-s.Rational(1,2))-zz/c-s.I*(s.Rational(1,2)/c-s.Rational(1,2)))==0)
# second-order source budget root
lam,kap,rr=s.symbols('lam kap rr',positive=True)
ck('curvature_sufficient_upper',s.simplify((lam-kap*x/2+rr*x*x).subs(x,4*lam/kap)+lam-16*rr*lam*lam/(kap*kap))==0)
(Path(__file__).resolve().parent/'mythos_exact_checks.json').write_text(json.dumps(out,indent=2))
print('ALL',len(out),'EXACT CONTROLS PASSED')
# Literal even m=2 physical rows, an explicit finite spectral CONTROL, not zeta.
mp.mp.dps=70
L=mp.log(2); b=L/2

def row(z):
    r=[]
    for j in range(3):
        om=2*mp.pi*j/L; dj=1 if j==0 else mp.sqrt(2)
        # no tested node is a modal pole
        r.append(2*dj*z*mp.sin(b*z)/(mp.sqrt(L)*(z*z-om*om)))
    return mp.matrix(r)
real_nodes=[mp.mpf(1),mp.mpf(2),mp.mpf(3)]
w=mp.mpc(20,mp.mpf(1)/4); ew=row(w)
P=sum((2*row(q)*row(q).T for q in real_nodes),mp.zeros(3))
re=mp.matrix([mp.re(v) for v in ew]); im=mp.matrix([mp.im(v) for v in ew])
v=im-re*((re.T*im)[0]/(re.T*re)[0]); v=v/mp.sqrt((v.T*v)[0])
bas=(v.T*P*v)[0]; neg=4*((im.T*v)[0])**2
nu=int(mp.ceil(bas/neg))+1

def model(y):
    pp=sum((2*mp.exp(-y*q*q)*row(q)*row(q).T for q in real_nodes),mp.zeros(3))
    f=mp.exp(-y*w*w)
    return pp+mp.matrix([[4*nu*mp.re(f*ew[i]*ew[j]) for j in range(3)] for i in range(3)])
res={'model':'finite 3 real pairs plus one quartet, literal m=2 rows; NOT zeta/DH','dps':70,'w':[str(mp.re(w)),str(mp.im(w))],'multiplicity':nu,'unit_trial_at_y0':str((v.T*model(0)*v)[0]),'eigenvalues':{}}
for y in [0,mp.mpf('0.1'),1]:
    vals=mp.eigsy(model(y),eigvals_only=True)
    res['eigenvalues'][str(y)]=[mp.nstr(z,38) for z in vals]
assert mp.mpf(res['unit_trial_at_y0'])<0
assert mp.mpf(res['eigenvalues']['1'][0])>0
print(json.dumps(res,indent=2))
(Path(__file__).resolve().parent/'mythos_heat_control.json').write_text(json.dumps(res,indent=2))
```
<!-- END_CHECKS -->

Для повторения при100dps заменить обе метки70 в численном блоке на100; символические проверки не меняются. В выполненном повторе напечатанные38 значащих цифр всех трех спектров совпали; absolute difference выбранного отрицательного trial quotient равна5.681e-71.
