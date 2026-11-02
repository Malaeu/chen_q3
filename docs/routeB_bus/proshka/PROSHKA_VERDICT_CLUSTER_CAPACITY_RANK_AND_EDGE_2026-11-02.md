# STATUS: TRY_PROJECTED_CLUSTER_CAPACITY_WITH_WEAK_RANK_BUDGET

```yaml
OPERATIVE_CLASS: TRY_PROJECTED_CLUSTER_CAPACITY_WITH_WEAK_RANK_BUDGET
DATE: 2026-11-02
TASK_MODE: DIRECT_OWNER_MATHEMATICAL_REQUEST
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
SOURCE_OPERATOR: LITERAL_EVEN_CCM_N_EQ_m_L_EQ_log_m_PHYSICAL_L2
SOURCE_INDEX_COMMIT: f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf
SOURCE_INDEX_BLOB: 84b6d256ed2cb30b71949bfcc465c148dbb15a82
SOURCE_RESIDUAL_COMMIT: 2176dab16bf77dd015f7efcb5a6f704587f732c8
SOURCE_RESIDUAL_BLOB: ebf7f8cab61a795118bda5dc7e65a0b3386247b7
SOURCE_AUDIT_COMMIT: e724ae65ed39a8ba8b8f07c928d790ea9820342a
SOURCE_ADAPTIVE_COMMIT: 3bdd5f8ffa106036b74cfaa0794f60155156d563
SOURCE_CAPACITY_COMMIT: bf890512b36abf2330d8f61a95f120cae58d0e0a
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
REQUESTED_LITERAL_CLUSTER_LOWER_BOUND: NOT_PROVED_OR_REFUTED
GENERAL_GEOMETRIC_THEOREM_SHAPE: REFUTED
SCOPED_KILL_SCOPE: THEOREM_SHAPE
SCOPED_KILL_EVIDENCE: SECTIONS_4_5_6_EXPLICIT_ORIGINAL_CARRIER_PLANTS_NOT_ZETA
NEW_LITERAL_SOURCE_RESULT: OUTER_ZERO_BAND_FORCES_GROWING_WEAK_CAPACITY_RANK
NEW_LITERAL_RESULT_SCOPE: COFINAL_FAMILY
NEW_LITERAL_RESULT_VERIFIER: PAPER_USING_PINNED_K_m_SUPPLIER
NEW_EXACT_REPAIR: MINIMAL_REMOVAL_RANK_AND_REPRESENTATIVE_PROJECTION_TRANSFER
NUMERICAL_CHECK: RAW_ZERO_EVALUATION_GRAM_85_AND_130_DPS
NUMERICAL_CHECK_CLASS: DIAGNOSTIC_NOT_INTERVAL
NEW_LITERAL_A_m_EIGENPROBLEMS: 0
RH_ASSUMED: false
SIMPLE_ZEROS_ASSUMED_FOR_SOURCE_THEOREM: false
REQUESTED_FORMULA_GAMMA_VERSUS_COMPLEX_ZERO_GUARD: RETAINED
INDEPENDENT_AUDIT_OF_NEW_DERIVATION: NOT_PERFORMED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
REPOSITORY_WRITTEN: false
RH_PROVED: false
ROUTE_PROMOTION: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
PX_RH_CLAIM: NOT_MADE
```

Ы. **Заявленная нижняя граница для настоящих нулей ζ после удаления не более одного направления на каждую нетривиальную группу здесь не доказана.** Её отрицание для этой конкретной ζ-семьи также не заявляется.

Получен более определённый результат, чем общий отказ от доказательства:

1. На исходном конечном carrier выведена явная верхняя оценка нормы внешнего evaluation-ядра. Вместе с уже проверенным `k_m` из 2176dab она доказывает **растущее число малых положительных собственных значений ёмкости на реальных исходных нулях**, когда берётся верхний moving-kappa график. Это не искусственная матрица и не численная экстраполяция.
2. Ранговое правило «не больше одного плохого направления на группу» опровергнуто как общая геометрическая теорема: кластер из s различных сливающихся узлов может дать s−1 плохих направлений. Для s=3 одного удаления недостаточно.
3. Даже при всех группах-одиночках остаются два независимых механизма: потеря ядра за модальной границей и локальное переполнение при глобально малом числе узлов. Даны точные контрсемьи на том же оконном carrier. Их узлы **не выдаются за нули ζ**.
4. Непосредственный пересчёт настоящих первых нулей показывает провал raw capacity уже в разрешённых конечных секторах, без близких групп при eta=1/4. Это floating-диагностика, не доказательство отсутствия любой сколь угодно малой кофинальной константы.

## 1. Источники, определения и граница задачи

### 1.1. Прочитанные источники

**[FINITE_CELL | PAPER: аудит определений и содержания файлов, не сертификация опубликованных чисел.]**

- **S1:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_2026-11-02.md`, commit `2176dab16bf77dd015f7efcb5a6f704587f732c8`, blob `ebf7f8cab61a795118bda5dc7e65a0b3386247b7`. Использованы определения J, физическая норма, теорема нижнего ранга и §3, особенно (3.9). Их аналитический вывод заново целиком не аудирован.
- **S2:** `docs/routeB_bus/proshka/SHRINKING_KAPPA_INTERPOLATION_RESIDUAL_PAPER_AUDIT_2026-11-02.md`, commit `e724ae65ed39a8ba8b8f07c928d790ea9820342a`; проверенный в commit текст независимого PAPER-аудита S1, SHA-256 `a52f2fd910bf298ae54b0a96fa4a3d31045aa278f6224c4ff3f3b1040ec30081`.
- **S3:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_QUIET_SPACE_INDEX_2026-11-02.md`, commit `f6c9cd89cc104ae3fdfc23bcc8a26b102d195fbf`, blob `84b6d256ed2cb30b71949bfcc465c148dbb15a82`. Прочитаны определения реального E_T, точный ранг (3.1), (3.2), полный индекс и §§7–8. В частности, независимость строк — точная полиномиальная интерполяция, не численный rank cutoff.
- **S4:** `docs/routeB_bus/quiet_space_kappa_2026-11-02/adaptive_threshold/RESULT.md`, commit `3bdd5f8ffa106036b74cfaa0794f60155156d563`, blob `38191320ba934eb36eb4b7e52095db5a32002268`; также родительский `quiet_space_kappa_2026-11-02/RESULT.md` при том же pin. Это FOUR размера m=16,24,32,40, а не все целые 16…40. Значение lambda_r около 2.2 относится к отдельным начальным секторам kappa, не ко всему допустимому диапазону.
- **S5:** `docs/routeB_bus/capacity_matrix_2026-11-02/{RESULT,NORMALIZATION}.md`, commit `bf890512b36abf2330d8f61a95f120cae58d0e0a`. Фактор 2 для двух знаков критического нуля, raw Fourier-нормировка и отсутствие безусловной положительности остатка сохраняются.

Bootstrap-протокол получен через GitHub с rh_clean. Никакие queue/state файлы не использованы для выбора другой задачи. Ответ адресован прямому запросу владельца; это не формальная TXT-транзакция bus.

### 1.2. Реальные ординаты — не подстановка для комплексных нулей

**[ABSTRACT | PAPER.]** В S1 пространство J задаётся значениями в фактических комплексных точках

\[
 z_\rho=\gamma+i(1/2-\beta),\qquad \rho=\beta+i\gamma,
\]

с использованием чётности для выбора положительной действительной части. В S3 E_T имеет одну вещественную строку для критической пары и две строки Re/Im для невещественной четвёрки. Условия на производные в кратных нулях не добавляются.

Выражение `sum |fhat(gamma_j)|^2` с одними вещественными ординатами совпадает с соответствующим value-map только для критических нулей. Проецировать все невещественные нули на прямую молча нельзя. Ниже:

- точные carrier-контроли уже работают для **различных вещественных узлов** — в наиболее благоприятном случае;
- новая кофинальная теорема §3 работает с исходным реальным E_T из S3, включая Re/Im-строки комплексных нулей;
- конечный численный тест использует первые критические нули, посчитанные заново, без вывода RH из этого факта.

### 1.3. Физическое ядро и положительная ёмкость

Положим

\[
 L=\log m,\quad \Delta=2\pi/L,\quad\Omega=m\Delta,
\]
\[
 \phi_n(x)=d_n(-1)^n\cos(n\Delta x)/\sqrt L,
 \quad |x|\le L/2,
 \quad d_0=1,\quad d_n=\sqrt2\ (n>0),
\]

с нулевым продолжением и n=0,…,m. Это тот же carrier V_m и ортонормированная физическая метрика.

Для вещественного t функционал f→fhat(t) имеет в V_m ядро

\[
 k_{m,t}=P_m(\cos(tx)\mathbf1_{[-L/2,L/2]}).
 \tag{1.1}
\]

Координатная строка равна

\[
 e_{m,n}(t)=\widehat\phi_n(t)
 =\frac{2d_nt\sin(tL/2)}{\sqrt L(t^2-n^2\Delta^2)},
 \tag{1.2}
\]

с непрерывным sinc-продолжением в модальных точках. Формула верна и для комплексного t.

После удаления точно нулевых строк и точных повторений q активных строк независимы при q≤m+1, по S3 (3.1)–(3.2). Положим

\[
 E=E_T,\quad J=\ker E,\quad H=J^\perp,
 \quad U^*U=I,\quad\operatorname{ran}U=H,\quad F=EU.
\]

Тогда **без построения U**:

\[
 \boxed{FF^*=EE^*.}\tag{1.3}
\]

Действительно, E=EUU* поскольку E аннулирует J. Поэтому положительные собственные значения E*E на H — ровно собственные значения q×q-матрицы C=EE*. Это положительная capacity-матрица. Она не отождествляется с полным A_m при возможных комплексных нулях.

## 2. Точная теорема о минимальном ранге удаляемых направлений

**Теорема 1. [ABSTRACT | PAPER.]** Пусть a>0 и

\[
 b_m(a)=\#\{j:0<\sigma_j(E)^2<a\}.
 \tag{2.1}
\]

Существует S⊂H размерности не больше b, такое что

\[
 \|Ef\|^2\ge a\|f\|^2
 \quad(f\perp J+S),
 \tag{2.2}
\]

**тогда и только тогда**, когда b_m(a)≤b.

**Доказательство.** На H оператор G=E*E положительно определён. Если спектральное пространство W для [0,a) имеет размерность b_m(a)>dim S, то W∩S^perp содержит ненулевой вектор; на нём Rayleigh quotient строго меньше a. Обратно, взять S=W. Равенство собственного значения a включено в хороший сектор и не удаляется. ∎

Следовательно, требуемое ранговое правило в запросе равносильно дополнительной source-оценке

\[
 \boxed{b_m(a(\eta))\le
 g_{m,\eta}:=\#\{\text{группы с хотя бы двумя различными активными узлами}\}.}
 \tag{2.3}
\]

Диаметр групп и выбор T в разрыве **не доказывают** (2.3). Ниже дано не только это переименование: выведены явные принудительные малые направления (§3) и три независимых геометрических контрсемьи (§§4–6).

## 3. Новый исходниковый результат: внешняя полоса вынуждает растущий слабый ранг

### 3.1. Универсальный конечный row budget

**Лемма 2. [FINITE_CELL | PAPER.]** Пусть z/Delta=w, Re w≥m+a, a>0, |Im z|≤1/2. Тогда

\[
 \boxed{\|e_m(z)\|_2^2
 \le \frac{2L\sqrt m}{\pi^2}(a^{-2}+a^{-1}).}
 \tag{3.1}
\]

Для вещественного z множитель sqrt(m) можно заменить на 1.

**Доказательство.** Перепишем (1.2):

\[
 e_{m,n}(z)=\frac{d_n\sqrt L}{\pi}
          \frac{w\sin(\pi w)}{w^2-n^2}.
\]

При Re w>m и n≥0 имеем |w/(w+n)|≤1 и |w−n|≥Re w−n. Кроме того,

\[
 |\sin(\pi w)|=|\sin(zL/2)|\le e^{L/4}=m^{1/4}.
\]

Таким образом,

\[
 \sum_{n=0}^m |e_{m,n}(z)|^2
 \le\frac{2L\sqrt m}{\pi^2}\sum_{j=0}^{m}(a+j)^{-2}
 \le\frac{2L\sqrt m}{\pi^2}(a^{-2}+a^{-1}).
\]

Последнее неравенство — первый член плюс интеграл от 0 до бесконечности. Для реального z используется |sin(zL/2)|≤1. Каждая из строк Re e и Im e имеет норму не больше нормы e. ∎

Это **верхняя** оценка нормы конкретного ядра. Она не является неудачной попыткой получить нижнюю оценку; она прямо даёт малые Rayleigh-значения положительного capacity Gram.

### 3.2. Подстановка фактических нулей из уже доказанного supplier

**Теорема 3. [COFINAL_FAMILY | PAPER, используя S1 (3.9), принятый аудитом S2.]** Пусть фиксировано 0<c<1 и

\[
 h=1+\log L,\quad \varepsilon=ch/L,
 \quad T=(1+\varepsilon)\Omega,
\]
\[
 U_0=(1+\varepsilon/3)\Omega,
 \quad V_0=(1+2\varepsilon/3)\Omega.
\]

Для всех достаточно больших m исходный E_T имеет не менее

\[
 p_m:=\left\lfloor\frac{\varepsilon\sqrt m}{96L}\right\rfloor
 =\left\lfloor\frac{c\sqrt m\,h}{96L^2}\right\rfloor
 \tag{3.2}
\]

независимых активных строк из полосы U_0<gamma≤V_0. Их q×q-Gram C=EE* удовлетворяет для каждого a_0>0:

\[
 \boxed{\#\{j:\sigma_j(F)^2<a_0\}
 \ge\max\left(0,p_m-
      \left\lfloor\frac1{8\pi^2a_0}\right\rfloor\right).}
 \tag{3.3}
\]

В частности, untrimmed sigma_min(F)^2→0; для каждой фиксированной положительной capacity-границы число необходимых удалений растёт к бесконечности.

**Доказательство.** S1 (3.9) даёт как минимум eps sqrt(m)/(96L) различных верхних неавтоматических нулей в указанной полосе, без предположения простоты или RH. Сопряжённая upper-пара complex-узлов даёт две реальные Re/Im-строки S3, критический узел — одну. Точные внешние sinc-автоматические строки уже исключены в S1. По S1 и S3 q_T≤N(T)<m+1 в конце последовательности, значит эти строки независимы.

Для каждой такой строки применяем (3.1) с a=eps m/3. При a≥1:

\[
 \|\text{row}\|^2\le
 \beta_m:=\frac{12L}{\pi^2\varepsilon\sqrt m}
 =\frac{12L^2}{\pi^2 c h\sqrt m}\longrightarrow0.
 \tag{3.4}
\]

Выберем любые p_m из этих строк и обозначим соответствующую главную подматрицу C через C_I. Она положительно определена, и

\[
 \boxed{\operatorname{tr}C_I\le p_m\beta_m
       \le\frac1{8\pi^2}.}\tag{3.5}
\]

В PSD-матрице с таким следом число собственных значений ≥a_0 не превосходит floor(1/(8 pi² a_0)). Значит у C_I как минимум указанное в (3.3) число значений <a_0. Интерлейсинг главных подматриц переносит этот нижний счёт малых значений на C=FF*. Это и есть (3.3). ∎

**Границы вывода.** Это source-specific теорема для raw E_T из f6c9cd8 и moving-kappa графика. Она не говорит, что плохих направлений больше g_(m,eta): такого сравнения с настоящими группами нулей пока нет. Поэтому исходный кластерно-обрезанный target для ζ не опровергнут. Но простое представление «малые направления возникают только из близких пар» не является достаточным анализом: внешний carrier-механизм необходимо оплатить.

### 3.3. Кратности и положительные веса

В S1 кратность любого нуля в выбранной полосе не превосходит 4L. Если включить multiplicity-веса в положительную capacity (повторив evaluation или умножив строку на квадратный корень веса), число независимых условий остаётся прежним. Для стандартных соглашений, учитывающих также ± и Re/Im, квадрат строкового множителя не больше 16L. Поэтому безопасная версия (3.5):

\[
 \operatorname{tr}C_{I,\mathrm{weighted}}\le 2L/\pi^2.
\]

Соответственно,

\[
 \boxed{b_m^{\mathrm{weighted}}(a_0)
 \ge\max\left(0,p_m-
          \left\lfloor\frac{2L}{\pi^2a_0}\right\rfloor\right).}
 \tag{3.6}
\]

Она тоже расходится, потому что p_m/L→infinity. Для одной положительной критической ординаты с весом nu можно использовать более сильный множитель 4L вместо 16L. Внешняя слабость не исчезает после честного учёта кратностей.

### 3.4. О cutoff gap

В (3.3) существенны узлы **внутри** (U_0,V_0], а не ближайший к T. Если T выбрать иначе, но сохранить всю эту полосу и q_T<m+1, доказательство не меняется. Для T≥V_0, выбранного в разрешённом большом gap, та же нижняя оценка слабого ранга действует. Здесь не доказывается существование такого gap для каждого m. Если разрешённый T лежит ниже V_0, нужно заново взять внутреннюю полосу, а не применять этот вывод молча.

## 4. Кластер из трёх: почему одного удаления недостаточно

**Теорема 4. [ABSTRACT | PAPER: тот же carrier, узлы этого контроля не являются ζ.]** Для фиксированного m≥3 выберем три различные внутренние немодальные частоты

\[
 t_0-a,\quad t_0,\quad t_0+a,
 \qquad 0<a\ll1,
\]

вдали от 0, Omega и T. Это одна изолированная группа диаметра 2a≤eta Delta.

Из (1.1) и контрактности P_m:

\[
 \|k_{m,t}-k_{m,s}\|_2
 \le |t-s|\left(\int_{-L/2}^{L/2}x^2dx\right)^{1/2}
 =|t-s|\sqrt{L^3/12}.
 \tag{4.1}
\]

Пусть E_a — три evaluation-строки, а E_0 — три одинаковые строки e_m(t_0). Тогда rank E_0=1 и

\[
 \|E_a-E_0\|_{\mathrm{HS}}^2\le L^3a^2/6.
\]

Два меньших собственных значения C_a=E_aE_a* поэтому не превосходят

\[
 \boxed{L^3a^2/6.}\tag{4.2}
\]

При a>0 и выбранных немодальных различных узлах все три строки независимы по полиномиальной интерполяции. Это **два малых положительных**, а не два точных нулевых значения, которые можно было бы спрятать в J.

Для любого S⊂J_a^perp с dim S≤1 по min–max найдётся единичный f⊥J_a+S с

\[
 \boxed{\sum_{j=1}^3|\widehat f(t_j)|^2\le L^3a^2/6.}\tag{4.3}
\]

Выбрав a настолько малым, что правая часть <a_0, получаем строгий верхний envelope для нарушения требуемой нижней границы a_0. Gap около T можно выбрать произвольно большим; он не меняет контроль.

Кофинальный вариант на исходном расписании: a_m=L^(-2), центр t_0=(floor(m/4)+1/2)Delta. Тогда группа имеет диаметр≤eta Delta для больших m, но правая часть (4.3)=1/(6L)→0.

**Обобщение.** При слиянии s различных активных узлов s строк стремятся к одной строке. s−1 положительных singular values могут стремиться к нулю. Для нескольких групп соответствующая worst-case потеря равна

\[
 \sum_C(|C|-1),
\]

а не числу групп с |C|≥2. Равенство этих двух бюджетов возможно для групп размера≤2. Это необходимая поправка к общей теореме, но сама по себе она **не доказывает** глобальную нижнюю границу: остаются §§5–6.

## 5. Одиночный внешний узел: провал без единого кластера

**Теорема 5. [ABSTRACT | PAPER: тот же carrier, synthetic real nodes.]** Возьмём для фиксированного 0<c<1

\[
 a_m=\left\lfloor\frac{cm(1+\log L)}{4L}\right\rfloor+\frac12,
 \quad t_m=(m+a_m)\Delta,
 \quad T_m=(m+2a_m)\Delta.
\]

Для больших m это допустимый диапазон

\[
 1<T_m/\Omega\le1+c(1+\log L)/L.
\]

Узел t_m один; кластеров размера≥2 нет. Он немодальный, поскольку a_m — полуцелое, и sin(t_m L/2)=±1. До cutoff T_m расстояние a_m Delta≫eta Delta. Следующий узел конфигурации можно поставить дальше T_m+eta Delta, так что cutoff находится в требуемом gap даже с запасом с обеих сторон.

Реальная версия (3.1) даёт

\[
 0<\|k_{m,t_m}\|^2
 \le\frac{2L}{\pi^2}(a_m^{-2}+a_m^{-1})
 =O_c\!\left(\frac{L^2}{m(1+\log L)}\right)\to0.
 \tag{5.1}
\]

На H=J^perp=span{k_(m,t_m)} единственный единичный вектор f=k/||k|| имеет

\[
 |\widehat f(t_m)|^2=\|k_{m,t_m}\|^2\to0.
\]

Ранговый бюджет пользователя равен нулю. Следовательно, «разделённость + cutoff gap + подкритический общий count» не дают требуемого lower bound даже без кластеров. Произвольная положительная a(eta) нарушается с явным отрицательным upper-envelope `right side of (5.1) - a(eta)` для больших m.

Это не только признак почти параллельных строк: здесь всего одна строка. Теряется её **норма после проекции на конечный carrier**. При желании контрпример можно вложить в один фиксированный разреженный набор частот, выбирая следующие m рекурсивно всё больше и исключая конечные наборы точных резонансов; независимость ранга сохраняется. Для опровержения геометрического вывода такая дополнительная упаковка не требуется.

## 6. Средняя плотность ниже критической недостаточна даже внутри полосы

**Теорема 6. [ABSTRACT | PAPER: distinct real nodes, все внутри Omega.]** Пусть 0<eta<d<1. Возьмём q=n+1≤m/4 узлов

\[
 t_j=t_0+jd\Delta,\qquad j=0,\ldots,n,
\]

внутри, например, (Omega/4,3Omega/4). Между любыми соседями gap=d Delta>eta Delta: все допустимые группы — одиночки. Весь набор содержит намного меньше m+1 узлов, а T=Omega можно поместить в большой конечный gap.

Положим

\[
 a_j=\frac{(-1)^j\binom nj}{\sqrt{\binom{2n}n}},
 \qquad \sum_j|a_j|^2=1.
\]

Тогда

\[
 \sum_{j=0}^n a_j e^{it_jx}
 =\frac{e^{it_0x}(1-e^{id\Delta x})^n}{\sqrt{\binom{2n}n}}.
\]

На |x|≤L/2:

\[
 |1-e^{id\Delta x}|\le2\sin(\pi d/2).
\]

Переход к вещественной части и затем ортопроекция P_m только уменьшают норму. Поэтому

\[
 \boxed{a^*EE^*a\le
 L\frac{4^n}{\binom{2n}n}\sin^{2n}(\pi d/2)
 \le L(2n+1)\sin^{2n}(\pi d/2).}\tag{6.1}
\]

Последняя оценка использует `binom(2n,n)≥4^n/(2n+1)`. При n proportional to m эта величина убывает экспоненциально. Полный ранг обеспечивается различными активными squared nodes. По (1.3) такой малый положительный eigenvalue принадлежит физической capacity на J^perp.

При eta=1/4,d=1/2 это особенно просто:

\[
 \lambda_{\min}(EE^*)\le L(2n+1)2^{-n}\longrightarrow0.
\]

Значит, исправить только локальные слияния и отрезать exterior недостаточно: нужен контроль **локальной плотности на всех relevant масштабах**, а не один суммарный count N(T).

## 7. Реальные ζ-данные: проверка именно raw capacity

**[FINITE_CELL | CONDITIONAL: floating diagnostics, не ARB_INTERVAL и не кофинальный вывод.]**

Прогнозы P1–P4 записаны до локальных тестов. Здесь не вычислялись A_m, prime sums или eigenvectors A_m. Пересчитаны первые 27 нулей `mpmath.zetazero`; из точных sinc-формул построен raw E и посчитана lambda_min(EE*). SVD-базис U не требуется благодаря (1.3). Строки **не нормировались**.

Первый проход: 85 decimal digits, прямой sinc. Проверка: свежие нули при 130 digits, независимая rational-times-sine запись. Это одна математическая матрица, два способа вычисления; повышение точности не называется независимым PAPER-аудитом или interval certificate.

Для разрешённого upper cutoff взято c=1/2. Когда нужно, T сдвинут **вниз в том же промежутке между нулями**, не меняя E и J, так чтобы оставался запас от обоих концов gap. Для eta=1/4 все внутренние gaps больше eta Delta, а расстояние от T до каждого из двух соседних нулей также больше eta Delta. Поэтому групп размера≥2 здесь нет ни при каком разбиении с заданным diameter bound.

|m|Допустимая κ после выбора gap|q|Минимальный внутренний gap / Δ|Запас T от ближайшего нуля / Δ|σ_min(F)²|
|---:|---:|---:|---:|---:|---:|
|16|1.348345292|9|1.06273738|0.39023413|6.2410960196e-09|
|24|1.327146109|14|0.75098314|1.08261197|3.6701643638e-15|
|32|1.317345623|19|0.81896323|0.39718528|1.4799998510e-21|
|40|1.312469243|25|0.81245517|0.35863861|1.2960220154e-23|

Для сравнения, в начальных секторах S4, откуда взято наблюдение о первой линии около 2.2:

|m|κ|2σ_min(F)²|
|---:|---:|---:|
|16|1.00|2.1745655952|
|24|1.02|2.2329046889|
|32|1.00|2.2484921377|
|40|1.00|2.1399836991|

Наихудшее относительное изменение восьми eigenvalues между двумя проходами — 1.952409e-64. Все проверки кластеров и cutoff-gap в таблице остаются численными.

**Что эта таблица опровергает и чего нет.** Она не поддерживает постоянную ёмкость порядка единицы на всём разрешённом диапазоне κ и показывает, что на этих четырёх срезах провал нельзя объяснить группами диаметра≤Delta/4: их просто нет. Но конечная таблица не опровергает существование какой-нибудь намного меньшей положительной константы после неизвестного m0. Кофинальный вывод об untrimmed capacity даёт §3, не эта таблица. Кластерно-обрезанный target остаётся отдельным вопросом о дефектном ранге.

## 8. Исправленная кластерная теорема с реальным нижним сертификатом

### 8.1. Что сохраняется после выбора представителя каждой группы

**Теорема 7. [ABSTRACT | PAPER.]** Пусть q различных активных evaluation-строк разбиты на g групп. Из каждой группы выберем одну действительную строку, получив E_R. Все выбранные строки независимы. Обозначим

\[
 W=\operatorname{ran}E_R^*\subset H,
 \qquad S=H\cap W^\perp.
\]

Тогда

\[
 \dim S=q-g=\sum_C(|C|-1),\qquad (J+S)^\perp=W.
 \tag{8.1}
\]

Если **дополнительно доказано**

\[
 E_RE_R^*\succeq aI_g,\tag{8.2}
\]

то для всех f⊥J+S

\[
 \boxed{\sum_{j=1}^q|\widehat f(t_j)|^2
 \ge\|E_R f\|^2\ge a\|f\|^2.}\tag{8.3}
\]

**Доказательство.** Первое неравенство — включение набора samples. Ненулевые собственные значения E_R*E_R на W совпадают со спектром E_RE_R*, так что (8.2) даёт второе. Размерность следует из rank E_R=g и dim H=q. ∎

Это не доказательство (8.2) для ζ. Теорема показывает правильный rank consumer и отделяет локальное удаление контрастов от глобальной capacity-оценки. Если группы состоят только из пар и одиночек, бюджет (8.1) равен числу нетривиальных групп, но обязательство (8.2) всё равно остаётся.

Кластерные средние тоже допустимы. Матрица B с одной нормированной constant-строкой на группу удовлетворяет BB*=I и ||BE f||≤||E f||. Можно взять E_R=BE и использовать его Gram вместо отдельных representatives. Это сохраняет реальные веса, но не превращает непроверенное lower bound в доказанное.

### 8.2. Полный Paley–Wiener Gram и цена проекции

**Теорема 8. [ABSTRACT | PAPER.]** Для выбранных вещественных representatives t_1,…,t_g положим в полном чётном L2-окне

\[
 k^\infty_t(x)=\cos(tx)\mathbf1_{[-L/2,L/2]}.
\]

Его Gram имеет явные элементы

\[
 C^\infty_{ij}=\frac L2\left[
 \operatorname{sinc}((t_i-t_j)L/2)+
 \operatorname{sinc}((t_i+t_j)L/2)\right].
\]

Пусть

\[
 D^{\mathrm{proj}}_{ij}=
 \langle(I-P_m)k^\infty_{t_i},(I-P_m)k^\infty_{t_j}\rangle.
\]

Тогда точно

\[
 \boxed{E_RE_R^*=C^\infty-D^{\mathrm{proj}},\qquad
 D^{\mathrm{proj}}\succeq0.}\tag{8.4}
\]

Следовательно,

\[
 C^\infty\succeq A I,\quad D^{\mathrm{proj}}\preceq B I,
 \quad A>B
 \quad\Longrightarrow\quad E_RE_R^*\succeq(A-B)I.
 \tag{8.5}
\]

**Доказательство.** Ортогональное разложение каждого полного ядра на P_m и I−P_m; смешанные Gram-блоки между этими ортогональными компонентами равны нулю. ∎

Вот где ломается прямой импорт Paley–Wiener lower bound: он относится к C^infinity, а пользователь просит оценку для C^infinity−D^proj. Сохранение exponential type L/2 не означает сохранение метрики на конечном carrier. В §5 полное ядро имеет норму порядка sqrt(L), а его проекция стремится к нулю; цена проекции принципиальна.

### 8.3. Проверенные междисциплинарные мосты

**[ABSTRACT | PAPER: проверка theorem shapes, не импорт отсутствующих ζ-предпосылок.]**

1. **Reproducing-kernel / finite frame duality.** Точное тождество FF*=EE* дало §3: можно считать ёмкость без собственного базиса дополнения и получить слабый ранг по следу выбранной внешней подматрицы.
2. **Confluent interpolation / divided differences.** Сливающиеся s evaluations имеют s−1 контрастов. Divided differences заменяют их на устойчивые jet-координаты, но обратный переход к raw values содержит множители малых расстояний. Поэтому lower bound в норме divided differences не даёт требуемый lower bound для исходной невзвешенной суммы.
3. **Paley–Wiener / Ingham-type interpolation.** В первичной работе Avdonin–Moran, Theorem 3(ii), используется верхняя **равномерная** плотность, а не средний count до одного T; Proposition 1 явно сохраняет gap-веса в групповых формах. Avdonin–Ivanov рассматривают Riesz-базы divided differences и дополнительные условия на generating function. В этой задаче не установлены необходимые равномерные по m константы этих условий и цена P_m. Даже теорема для каждого фиксированного конечного набора не предоставляет общего lower bound для растущей семьи.

Primary references, checked in original text (PDF screenshot calls failed with cache-miss; accessible parsed/HTML mathematical text was read):

```text
Avdonin, S.; Moran, W. (2001).
Ingham-type inequalities and Riesz bases of divided differences.
Int. J. Appl. Math. Comput. Sci. 11(4), 803–820.
Theorem 3 and Proposition 1, printed pp.808–809.
https://matwbn.icm.edu.pl/ksiazki/amc/amc11/amc1143.pdf

Avdonin, S.A.; Ivanov, S.A. (2001 preprint).
Exponential Riesz bases of subspaces and divided differences.
https://arxiv.org/abs/math/0103160
```

## 9. Контраргументы, re-representations и минимальный остаток

### Сильнейшая атака на вывод этого документа

«Synthetic узлы не являются ζ, значит кластерная теорема на фактических нулях может оказаться верной». **Да.** Поэтому generic geometric shape refuted, но literal target NOT_PROVED_OR_REFUTED. Специальная арифметика ζ могла бы доказать (2.3) вместе с подходящим выбором S. Никакое заключение о наличии близкой тройки ζ или о сравнении p_m с настоящим g_(m,eta) здесь не сделано.

«После добавления большого числа групп разрешённый rank budget может превосходить p_m». **Да.** §3 тогда не противоречит требуемому lower bound после удаления, но требует показать, что удалены все соответствующие слабые направления. Число групп само по себе не задаёт это подпространство.

«Можно выбрать T близко к Omega, избегая внешней полосы». **Да.** Теорема §3 дана для upper moving-kappa графика либо cutoff, сохраняющего внутреннюю полосу. Она не опровергает возможную теорему на другом выбранном подграфике. Но остаточная невязка S1 не равномерна до kappa=1, и этот возврат требует снова проверить downstream-пакет, а не взять residual с верхнего графика и capacity с нижнего.

### Кандидаты смены представления

| Представление | Что точно сохраняется | Дискриминатор | Kill-power / cost |
|---|---|---|---|
| Projected block means + exact defect rank | исходные raw samples и carrier; условный бюджет (8.3) | lower envelope smallest eigenvalue of C^infinity−D^proj; отдельно count b_m(a) | 9/10 / 3/10 для finite проверки, cofinal supplier отдельный |
| Confluent/DD coordinates с явным value-metric | все узлы/кратности; не меняется вывод без обратной metric-оплаты | минимальное собственное значение метрического блока после удаления s−1 контрастов | 8/10 / 5/10; показывает, что потеря локальная или глобальная |
| Source exterior weak-rank trace | исходные complex ζ и точный carrier | (3.5), затем b_m(a) против actual group budget | 10/10 / 1/10 для inherited cofinal supplier; это выбранный ход |

**Минимальное незакрытое обязательство пользователя:** для конкретного алгоритма группировки и одного a(eta)>0 доказать на исходной семье

\[
 b_m(a(\eta))\le g_{m,\eta},
\]

и предъявить подпространство S_m допустимого ранга, чей orthogonal complement избегает всех малых capacity-направлений. Это обязательство нельзя заменить ни размерностью J, ни общей плотностью, ни similarity eigenvectors A и 2E*E.

**DISCRIMINATOR:** capacity-Rayleigh quotient в физически нормированном surviving направлении; для сертификата нарушения — строгий upper envelope `||Ef||²-a||f||²<0`. Для положительного сертификата — lower envelope на всём surviving compression. Exact zero rows определять по sinc/modal algebra, а не numerical-rank tolerance. Zero-consistent маленькое значение не даёт ни lower bound, ни точного нуля.

## 10. Dependency epistemics

```yaml
DOWNSTREAM_CONSUMER: SOURCE_SCHUR_THRESHOLD_FLOOR_FROM_f6c9cd8
ACTUAL_CONSUMER_REQUIREMENT: FULL_SIGNED_SCHUR_LOWER_BOUND_OR_OTHER_CONSTANT_FLOOR_INTERFACE
ORIGINAL_REQUESTED_OBJECT: CLUSTER_TRIMMED_RAW_CAPACITY_LOWER_BOUND_WITH_ONE_LOSS_PER_NONTRIVIAL_GROUP
ORIGINAL_OBJECT_IS: UNKNOWN_AS_NECESSARY
KNOWN_WEAKER_INTERFACES:
  - SIGNED_FULL_SCHUR_LOWER_ENVELOPE_CAN_SUFFICE_WITHOUT_SEPARATE_RAW_CAPACITY_FLOOR
  - CAPACITY_PLUS_PAID_TAIL_AND_THRESHOLD_METRIC_IS_A_SUFFICIENT_INTERFACE_NOT_COMPLETE_HERE
  - REPRESENTATIVE_GRAM_MINUS_PROJECTION_LOSS_IMPLIES_CLUSTER_TRIMMED_RAW_BOUND_WITH_SUM_s_MINUS_1_RANK
FAILURE_TYPE_LITERAL: NO_DERIVATION
EPISTEMIC_STATUS_LITERAL: RESEARCH_DEBT
REOPEN_TRIGGER_LITERAL: UNIFORM_PROJECTED_BLOCK_FRAME_OR_EXACT_WEAK_RANK_VERSUS_GROUP_COUNT_BOUND
FAILURE_TYPE_GENERAL_GEOMETRIC_SHORTCUT: COUNTEREXAMPLE
EPISTEMIC_STATUS_GENERAL_SHAPE: MATHEMATICALLY_DEAD
KILL_SCOPE_GENERAL_SHAPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: PAPER_UPPER_ENVELOPES_TENDING_TO_ZERO_ON_SAME_CARRIER
KILL_EVIDENCE_REFERENCE: SECTIONS_4_5_6_OF_THIS_ARTIFACT
ROUTE_FAMILY_DEATH: NOT_ASSERTED
NOVELTY_AXIS: PROJECTED_KERNEL_ESCAPE_AND_SOURCE_WEAK_RANK_NOT_ANOTHER_ZERO_COUNT_FIT
```

## 11. Meta closeout и реестр утверждений

| Утверждение | Scope | Verifier | Граница |
|---|---|---|---|
| (1.3), Theorem 1 | ABSTRACT | PAPER | точная duality и оптимальный defect rank |
| (3.1) | FINITE_CELL | PAPER | finite carrier upper на внешние строки, все complex offsets |
| (3.3)–(3.6) | COFINAL_FAMILY | PAPER | inherited S1 k_m; не новый upper count для A |
| §§4–6 | ABSTRACT | PAPER | контрсемьи geometric shortcut; узлы не ζ |
| §7 | FINITE_CELL | CONDITIONAL | 85/130dps diagnostic, не interval certificate |
| (8.1)–(8.5) | ABSTRACT | PAPER | корректная импликация при оплаченной projected Gram lower bound |
| requested literal lower bound | COFINAL_FAMILY | CONDITIONAL | реальный источник uniform projected frame остаётся открыт |

**Что стало меньше:** generic требование «плотность ниже критической, удалить одно направление на группу» заменено точным ранговым счётчиком и двумя раздельными расходами: confluent rank и finite-carrier projection. Для исходного moving-kappa E доказан растущий нижний defect rank.

**Что убито:** только общая theorem shape из diameter + overall density + cutoff gap; внутри неё отдельно один-per-triple, перенос full PW bound без projection fee и замена local density суммарным count. Не RH, не Route B и не вся literal cluster-family.

**Что не повторять:** raw E не заменять row-normalized E; не брать capacity одного kappa и residual другого; не считать небольшой angle между eigenvectors lower eigenvalue certificate; не приписывать всякий слабый singular mode близкой паре.

**Судьба зарегистрированных прогнозов:**

- P1 подтверждён PAPER-доказательством (4.1)–(4.3); три конечных floating-контроля согласуются с ним.
- P2 подтверждён PAPER-доказательством (3.1)/(5.1); три finite numeric controls. Затем получено более сильное source-следствие §3.
- P3 подтверждён точным binomial witness (6.1), 33 символическими binomial проверками и тремя finite Gram Rayleigh controls.
- P4 подтверждён только на зарегистрированных finite diagnostics: ранние сектора сохраняют 2 sigma_min²≈2.14–2.25, допустимые верхние сектора дают 10^−8…10^−23. Никакого ретроактивного превращения P4 в кофинальный прогноз.

```yaml
iteration:
  target: CLUSTER_STABLE_RAW_ZERO_CAPACITY
  status: PROGRESS
  failed_strategy: INFER_UNIFORM_FRAME_FROM_TOTAL_DENSITY_AND_ONE_LOSS_PER_GROUP
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: FINITE_CARRIER_KERNEL_IS_PROJECTED_AND_CONFLUENT_LOSS_IS_s_MINUS_1
  forbidden_future_move: BORROW_FULL_PALEY_WIENER_FRAME_CONSTANT_WITHOUT_PROJECTION_CONTROL
  next_decisive_test: CERTIFIED_WEAK_RANK_AND_LOCALIZATION_OF_SURVIVING_BAD_VECTORS
```

## 12. CODEX DIRECTIVE

**Одна следующая задача:** на уже сохранённых четырёх carrier-ячейках подтвердить interval/Rayleigh upper-сертификатом finite внешний дефект raw E, начиная с m=40, eta=1/4 и cutoff κ=1.3124692429827545… из §7. Не пересчитывать A, не расширять сетку m и не менять carrier. Из точного raw E предъявить физически нормированное f∈J^perp и доказать `||Ef||²<10^−20`, одновременно сертифицировав отсутствие пар на расстоянии≤Delta/4 и clearance T от соседних нулей>Delta/4. Можно использовать сохранённый floating singular vector только как trial; остатки zero values, quadrature (если она вообще нужна), Gram и normalization оплатить интервалами. Успех подтверждает finite structural discriminator, **не** отрицание любой кофинальной a(eta)>0. При невозможности получить strict upper вернуть точное пересекающее ноль неравенство, не придумывать отрицательный вердикт.

No repository writes or Lean source changes were made by this response. The committed artifacts at the supplied pins remain immutable.

## Appendix A. Registered predictions and reproducibility

The following registration was written before the numerical runs. All scripts below concern diagnostics only. Exact symbolic controls and PAPER inequalities remain separate from floating calculations.

```json
{
 "date":"2026-11-02",
 "predictions":[
  {"id":"P1","test":"three distinct real evaluations coalescing in the original even carrier","prediction":"two nonzero singular values tend to zero; deleting any one physical direction cannot leave a uniform lower bound","scope":"ABSTRACT_CARRIER_CONTROL_NOT_ZETA"},
  {"id":"P2","test":"one nonresonant exterior real sample with T in the permitted moving-kappa range","prediction":"raw row squared norm decays O(L^2/(m*(1+log L))); no close-pair collision is necessary","scope":"ABSTRACT_CARRIER_CONTROL_NOT_ZETA"},
  {"id":"P3","test":"equally spaced subcritical-total-count block with local spacing d*2pi/L, eta<d<1","prediction":"a binomial synthesis witness gives exponentially small Gram Rayleigh value despite no close groups","scope":"ABSTRACT_CARRIER_CONTROL_NOT_ZETA"},
  {"id":"P4","test":"actual first zeta zeros m=16,24,32,40 at selected cutoff sectors and c=1/2 moving cutoffs","prediction":"the approximate first-level 2.2 observation will not give a kappa-uniform raw capacity floor; raw smallest singular value decreases when additional exterior rows enter","scope":"FINITE_CELL_FLOATING_DIAGNOSTIC"}
 ]
}
```

Save the three code blocks below as the indicated filenames in one directory. Run:

```sh
uv run --with mpmath python diagnostics.py
uv run --with mpmath python validate.py
uv run --with sympy --with mpmath python exact_and_block_checks.py
```

There are no placeholders: the files write diagnostic JSON next to themselves. They do not access or modify the repository.

### diagnostics.py

```python
"""Finite controls only; no interval or cofinal certification."""
from pathlib import Path
import json, time
import mpmath as mp
mp.mp.dps=85
ROOT=Path(__file__).parent

def row(m,t):
    L=mp.log(m); D=2*mp.pi/L
    ans=[]
    for n in range(m+1):
        d=1 if n==0 else mp.sqrt(2)
        x=(t-n*D)*L/2; y=(t+n*D)*L/2
        sinc=lambda z: mp.sin(z)/z if z else mp.mpf(1)
        ans.append(d*((-1)**n)*mp.sqrt(L)/2*(sinc(x)+sinc(y)))
    return ans

def eigs(m,ts):
    E=mp.matrix([row(m,t) for t in ts])
    return list(mp.eigsy(E*E.T,eigvals_only=True))

start=time.monotonic(); controls=[]
m=32; L=mp.log(m); D=2*mp.pi/L; t0=mp.mpf('5.5')*D
for a in ['0.01','0.0001','0.000001']:
    a=mp.mpf(a); ev=eigs(m,[t0-a,t0,t0+a]); bound=L**3*a*a/6
    assert ev[1]>0 and ev[1]<=bound
    controls.append(dict(kind='triple',m=m,spacing=str(a),lambda1=str(ev[0]),lambda2=str(ev[1]),bound=str(bound)))
for m in [100,1000,10000]:
    L=mp.log(m); h=1+mp.log(L); a=mp.floor(mp.mpf('0.5')*m*h/(4*L))+mp.mpf('.5')
    u=m+a; t=2*mp.pi*u/L
    # Closed rational row, summed directly.
    v=L/mp.pi**2*mp.fsum([(1 if n==0 else 2)*u*u/(u*u-n*n)**2 for n in range(m+1)])
    bound=2*L/mp.pi**2*(1/a**2+1/a)
    assert v<=bound
    controls.append(dict(kind='exterior',m=m,a=str(a),row_norm_sq=str(v),bound=str(bound)))
(ROOT/'control_results.json').write_text(json.dumps(controls,indent=2))
print('6 analytic-bound numerical controls passed; DIAGNOSTIC ONLY',flush=True)

zeros=[]
for k in range(1,28):
    zeros.append(mp.im(mp.zetazero(k)))
    if k%9==0:
        used=time.monotonic()-start; eta=used*(27-k)/k
        print(f'zeros [{"#"*(k//3):<9}] {k}/27 ETA {eta:.1f}s',flush=True)
(ROOT/'zeros_85dps.json').write_text(json.dumps([str(z) for z in zeros],indent=2))
res=[]
for m in [16,24,32,40]:
    L=mp.log(m); D=2*mp.pi/L; Om=m*D; h=1+mp.log(L)
    # Pinned near-Omega sector and c=1/2 moving cutoff.
    for tag,kap in [('early',mp.mpf('1.02') if m==24 else mp.mpf(1)),('c_half',1+h/(2*L))]:
        T=kap*Om; ts=[z for z in zeros if z<T]
        assert zeros[-1]>T
        ev=eigs(m,ts)
        mingap=min([ts[j+1]-ts[j] for j in range(len(ts)-1)])/D
        nextz=zeros[len(ts)]; cutgap=(nextz-ts[-1])/D
        res.append(dict(m=m,tag=tag,kappa=str(kap),q=len(ts),sigma_min_sq=str(ev[0]),two_sigma_min_sq=str(2*ev[0]),min_internal_gap_units=str(mingap),cut_gap_units=str(cutgap),T_left_dist_units=str((T-ts[-1])/D),T_right_dist_units=str((nextz-T)/D)))
        print(m,tag,'q',len(ts),'sigma_min^2',mp.nstr(ev[0],12),'min gap/Delta',mp.nstr(mingap,8),flush=True)
(ROOT/'actual_zero_capacity_85dps.json').write_text(json.dumps(res,indent=2))
print(f'Done in {time.monotonic()-start:.2f}s; FLOATING NOT INTERVAL',flush=True)
```

### validate.py

```python
from pathlib import Path
import json,time
import mpmath as mp
P=Path(__file__).parent
old=json.loads((P/'actual_zero_capacity_85dps.json').read_text())
mp.mp.dps=130
zs=[mp.im(mp.zetazero(k)) for k in range(1,28)]
res=[]
for r in old:
    m=r['m']; L=mp.log(m); D=2*mp.pi/L; Om=m*D
    cap=(mp.mpf('1.02') if m==24 else mp.mpf(1))*Om if r['tag']=='early' else (1+(1+mp.log(L))/(2*L))*Om
    ts=[z for z in zs if z<cap]; q=len(ts)
    E=mp.matrix([[2*(1 if n==0 else mp.sqrt(2))*t*mp.sin(t*L/2)/(mp.sqrt(L)*(t*t-(n*D)**2)) for n in range(m+1)] for t in ts])
    ev=mp.eigsy(E*E.T,eigvals_only=True); v=ev[0]
    rel=abs(v-mp.mpf(r['sigma_min_sq']))/abs(v)
    assert rel<mp.mpf('1e-50')
    Tout=cap if r['tag']=='early' else min(cap,(ts[-1]+zs[q])/2)
    if r['tag']=='c_half':
        assert Tout>=Om and Tout<=cap
        assert min(Tout-ts[-1],zs[q]-Tout)/D>mp.mpf('.25')
        assert min(ts[j+1]-ts[j] for j in range(q-1))/D>mp.mpf('.25')
    x=dict(m=m,tag=r['tag'],q=q,value=str(v),relative_change=str(rel),adjusted_kappa=str(Tout/Om),adjusted_cut_clearance_units=str(min(Tout-ts[-1],zs[q]-Tout)/D))
    res.append(x)
    print(m,r['tag'],'relative_change',mp.nstr(rel,6),'adjusted_kappa',mp.nstr(Tout/Om,9),'clearance',mp.nstr(min(Tout-ts[-1],zs[q]-Tout)/D,6))
(P/'validation_130dps.json').write_text(json.dumps(res,indent=2))
print('ALL EIGHT CHECKS PASSED: 85dps/sinc vs fresh 130dps/rational; NOT INTERVAL')
```

### exact_and_block_checks.py

```python
from pathlib import Path
import json
import sympy as s
import mpmath as mp
L,m,c,h,eps=s.symbols('L m c h eps',positive=True)
p=eps*s.sqrt(m)/(96*L)
b=12*L/(s.pi**2*eps*s.sqrt(m))
assert s.simplify(p*b-1/(8*s.pi**2))==0
x=s.symbols('x',real=True)
assert s.integrate(x*x,(x,-L/2,L/2))==L**3/12
w=s.symbols('w')
for n in range(1,12):
    assert s.expand(sum((-1)**j*s.binomial(n,j)*w**j for j in range(n+1))-(1-w)**n)==0
    assert sum(s.binomial(n,j)**2 for j in range(n+1))==s.binomial(2*n,n)
    assert s.binomial(2*n,n)*(2*n+1)>=4**n
print('EXACT: trace product, derivative norm and 33 binomial identities passed')
mp.mp.dps=100
out=[]
for M in [64,128,256]:
    ell=mp.log(M); D=2*mp.pi/ell; q=M//4; n=q-1; d=mp.mpf('.5'); t0=(mp.mpf(M)/4+mp.mpf('.125'))*D
    zs=[t0+j*d*D for j in range(q)]
    norm=mp.sqrt(mp.binomial(2*n,n)); coeff=[(-1)**j*mp.binomial(n,j)/norm for j in range(q)]
    def rr(t,k):
        return 2*(1 if k==0 else mp.sqrt(2))*t*mp.sin(t*ell/2)/(mp.sqrt(ell)*(t*t-(k*D)**2))
    vec=[mp.fsum(coeff[j]*rr(zs[j],k) for j in range(q)) for k in range(M+1)]
    energy=mp.fsum(v*v for v in vec)
    bound=ell*(2*n+1)*mp.sin(d*mp.pi/2)**(2*n)
    assert 0<energy<=bound
    out.append({'m':M,'q':q,'gram_rayleigh':str(energy),'upper_bound':str(bound),'spacing_in_Delta':'0.5'})
    print('local-density plant',M,'Rayleigh',mp.nstr(energy,8),'upper',mp.nstr(bound,8))
Path(__file__).with_name('local_density_controls.json').write_text(json.dumps(out,indent=2))
```

## Appendix B. Recorded controls

### control_results.json

```json
[
  {
    "kind": "triple",
    "m": 32,
    "spacing": "0.01",
    "lambda1": "0.000000002226956868540973881587055684191768914578899989045851461315907982495142997509158994546",
    "lambda2": "0.0003477501072325677285160656291014591965200622969777548538963986820220578243139661918495",
    "bound": "0.0006938013583102697494142782971077719669919301778095971924816913396330260929251479663678"
  },
  {
    "kind": "triple",
    "m": 32,
    "spacing": "0.0001",
    "lambda1": "0.00000000000000002226901841689953796009695623557239484363596639276410016728820672825998272150469505128",
    "lambda2": "0.00000003477711121397006657663132599141872822876771557929299434152226783141865726281893006476",
    "bound": "0.00000006938013583102697494142782971077719669919301778095971924816913396330260929251479663678"
  },
  {
    "kind": "triple",
    "m": 32,
    "spacing": "0.000001",
    "lambda1": "0.0000000000000000000000002226901836187036007370767214734756886222573335042875698686118620353900562265688331115",
    "lambda2": "0.000000000003477711142402519932288690306648997222575012434138935898600656276711474491876937695956",
    "bound": "0.000000000006938013583102697494142782971077719669919301778095971924816913396330260929251479663678"
  },
  {
    "kind": "exterior",
    "m": 100,
    "a": "6.5",
    "row_norm_sq": "0.04542159813876540401512393456923825382875486065190917719523099326002720061785123791285",
    "bound": "0.1656572641841603061688333799926973420345975293415497673391788811074966904184434989916"
  },
  {
    "kind": "exterior",
    "m": 1000,
    "a": "53.5",
    "row_norm_sq": "0.007647136209807522635299541931834492875048317825138486731853618006079430191737408584351",
    "bound": "0.02665361571784799545756030826138071218114526236353121027299339827828802982092888195409"
  },
  {
    "kind": "exterior",
    "m": 10000,
    "a": "437.5",
    "row_norm_sq": "0.001216804792554042692952455196146011808587799881259863884349532436337392916572411263509",
    "bound": "0.004275819989599251410407845746739835847396798452906512660313115777843445024564030052317"
  }
]
```

### local_density_controls.json

```json
[
  {
    "m": 64,
    "q": 16,
    "gram_rayleigh": "0.00001941829578708588672035971472561705030736211103745462430719182853738138943185356477232368679289145984",
    "upper_bound": "0.003934490221684259874011388384741846974549652862274398109937941948418310964549658725057695886881526974",
    "spacing_in_Delta": "0.5"
  },
  {
    "m": 128,
    "q": 32,
    "gram_rayleigh": "0.000000000246537608944653825385216834077350265746181276357374482794064772017348726462286839887110895168337292",
    "upper_bound": "0.0000001423423675014338835389350380576475833176148865618149596579465475802247353310861483133331533546655631",
    "spacing_in_Delta": "0.5"
  },
  {
    "m": 256,
    "q": 64,
    "gram_rayleigh": "0.000000000000000000046605874564923425872941511606197055780882522678256545161290638165224831441416284351375234460155943",
    "upper_bound": "0.00000000000000007635358658795396288170409476828532509411598833810217001304001504183044216601055916184753955036725498",
    "spacing_in_Delta": "0.5"
  }
]
```

### validation_130dps.json

```json
[
  {
    "m": 16,
    "tag": "early",
    "q": 5,
    "value": "1.087282797605012980828863528904104810081774934348284136262392479714924250021378452654151252506676813813121564282619119055916339637",
    "relative_change": "1.391105488010863151058205913035083502301878048742305801442617664249777437378585799461251986074779075662178721986246080607251243719e-85",
    "adjusted_kappa": "1.0",
    "adjusted_cut_clearance_units": "0.5856979510339745177336467854631020914487073637552077568353208135811532279377888457885863214599606875884926644271008182570198352011"
  },
  {
    "m": 16,
    "tag": "c_half",
    "q": 9,
    "value": "0.00000000624109601958056539532824165012616544821870608982606600131616349529001802608501649807282794870821229975386840964715119889399470255",
    "relative_change": "1.514619089723054036080434120813946327702150447949139535029140072112361972889876081607578473456966092404188848970473056816747838147e-78",
    "adjusted_kappa": "1.348345292230854849535711534284544068676121531486991151093834301747962224445113935102374116642345009558093356173432048369312865127",
    "adjusted_cut_clearance_units": "0.3902341255238620723355931206664254258300955908072375229082033301824311500086624833102820395119488732454115341821692310314245146368"
  },
  {
    "m": 24,
    "tag": "early",
    "q": 9,
    "value": "1.116452344470830458965591723175045918115417297067778706191807516007736448663930948849954026333144439323438875377087256201096385261",
    "relative_change": "4.117835130468645826667969719166581230489362949923304657940451499590095194907133142922776983423964470883835185663392276211977835234e-86",
    "adjusted_kappa": "1.02",
    "adjusted_cut_clearance_units": "0.1988517963976415710038420499245922028069843995058055190825781713956897934802302733152755967380717990463982791705563703378312865578"
  },
  {
    "m": 24,
    "tag": "c_half",
    "q": 14,
    "value": "0.000000000000003670164363834378441582973125115464505980429270724520636436245468686212252396735928847073746212310801623757729268876858291117978206",
    "relative_change": "2.506225156987590069264961480764976338063115645009753551651893577050403933429424451526590500895887638461749720515790825533027166016e-72",
    "adjusted_kappa": "1.327146109001160514909594728741713869255262650697323640686974244533160640994231696097574226635837029241300514297135395721517699399",
    "adjusted_cut_clearance_units": "1.082611971761007895010493009890737546082787560999627418188080100089663551655811026769302164603083932316290858840685068275747011605"
  },
  {
    "m": 32,
    "tag": "early",
    "q": 12,
    "value": "1.12424606887205028546697261234764765989744908461751648821995158123564876518084113395955890929808457719484781255402553972124782078",
    "relative_change": "3.923435572765369849868630792706781407762572246673448208339027889336076808651549257987672630101008379040958938147672431020884577601e-85",
    "adjusted_kappa": "1.0",
    "adjusted_cut_clearance_units": "0.7351766769999814087702330819381009386916466382954352314238468252456815142770625544004906800984085710115279344227278749493670419471"
  },
  {
    "m": 32,
    "tag": "c_half",
    "q": 19,
    "value": "0.000000000000000000001479999850995458074403009896559142570609432750450264221737808493136849623205005786888996780714716395122465893132951447030458472523",
    "relative_change": "3.174307696445242898932484697513208642241685923656860356012534535376648282429570454508023285660978310593300319674998558304318784236e-65",
    "adjusted_kappa": "1.317345623204678182612045627415662169044849485393838530065287494847482155015544448035277741733079427107944319897713306255894398012",
    "adjusted_cut_clearance_units": "0.3971852756415900741985403674345791822315590779843113704407181422533135733690709457663243958602066142717116713700306975679862774582"
  },
  {
    "m": 40,
    "tag": "early",
    "q": 16,
    "value": "1.069991849549852508141859607367304508462260813598696419823268963044664059925525615241064494765130405641218474468755492345401033911",
    "relative_change": "6.027594056677974199897009203410048659312372552963189418864791302458168555955335756781486042510918222074027934985021269647621059578e-86",
    "adjusted_kappa": "1.0",
    "adjusted_cut_clearance_units": "0.6172151941222177834095026808212567806682046461072825069524954618014991508790858635252419088538680163361426911019941921519090221779"
  },
  {
    "m": 40,
    "tag": "c_half",
    "q": 25,
    "value": "0.00000000000000000000001296022015408507224824708973356985820277703906923593591387009257779829407572208686468178017904648931272981319112576099650555931466",
    "relative_change": "1.952408520828150031428407180156228335047433100043085161744614322078108224130436395320203270570854376374344546868804483403139095165e-64",
    "adjusted_kappa": "1.312469242982754502004086133241029216257962052163290154177415377503531588984367414715305707406446755655830822401290397724866583766",
    "adjusted_cut_clearance_units": "0.3586386145315403272780031960934143669628445814966242350430893796037207663322063264396002091783912102707251994748816043802297378347"
  }
]
```
