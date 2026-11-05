# STATUS: TRY_ROUND7_NB_FINITE_HORIZON_COUPLING_B

```yaml
OPERATIVE_CLASS: TRY_ROUND7_NB_FINITE_HORIZON_COUPLING_B
DATE: 2026-11-06
ANSWER: PARTIAL_QUANTITATIVE_BRIDGES_AND_RECEIVER_COUPLING
FULL_REQUEST_ACCEPTANCE: NOT_COMPLETE
REQUEST_COMMIT: 195366c6a61cd1fc457b0a302e58b33b1936528e
REQUEST_BLOB: e43e2bb5430b266b8c52eb489d7b882a261c17a9
PROTOCOL_BLOB: 32a5337b8b3bd431126084f250baf73f86e8f749
SPEC_FREEZE_COMMIT: 97f4cf0380adf863bb8cd4c663fc05b2a30488b3
SPEC_FREEZE_BLOB: 27dd83d293ef2150a34cd01040e80f4d7c6fbe34
SPEC_FREEZE_PATH: docs/routeB_bus/proshka/PROSHKA_FREEZE_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md
SPEC_CHANGED_AFTER_FREEZE: false
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md
PROVED_STEPS:
  - {id: EXACT_CENTERED_NB_CONSTRAINT_AND_RANK_ONE_DISTANCE_RELATION, scope: FINITE_CELL, verifier: PAPER}
  - {id: dN_SQUARED_LE_eN_LE_KAPPA_dN_SQUARED, scope: FINITE_CELL, verifier: PAPER}
  - {id: FULL_WINDOW_THRESHOLD_m_MINUS_1_WITH_CONSTANT_36000, scope: FINITE_CELL, verifier: PAPER}
  - {id: CRITICAL_POWER_ONE_WITHIN_INHERITED_C20_ENVELOPE, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: NB_ERROR_TO_GAUSSIAN_TIME_HORIZON_EXPLICIT_CONSTANT, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXPLICIT_WEIGHTED_SOURCE_NORM_PAYS_WINDOW_ERRORS, scope: ABSTRACT, verifier: PAPER}
  - {id: NEAR_EDGE_GAUSSIAN_RECEIVER_HAS_EXPONENT_THETA, scope: COFINAL_FAMILY, verifier: PAPER}
  - {id: QUASIPOLYLOG_PREFIX_RATE_EQUIVALENT_TO_RH, scope: COFINAL_FAMILY, verifier: PAPER}
RH_GAP: "Unconditional proof of e_m <= 1/(2 log m) eventually, or of the stated slower-prefix rate; no optimal one-cell whole-window bridge at an inverse-polylog threshold has been proved."
PROGRESS_CLASS: PROOF_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS:
  - id: IMPORTING_POSITIVE_POWER_VN_ERROR_AS_OPTIMIZED_NB_DISTANCE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_UPPER_BOUND_ONE_VERSUS_POSITIVE_POWER_LOWER_BOUND
    EVIDENCE: SECTION_8
    FAILURE_TYPE: COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
DOES_NOT_KILL: [RH, N_EQ_m_RECEIVER_COUPLING, SOURCE_SPECIFIC_WHOLE_WINDOW_BRIDGES, MAIER_RASSIAS_THEOREM]
CLOSES:
  - CENTERING_AND_NORM_CONVENTION_GAP
  - EXCESS_m_MINUS_6_FOR_POLYLOG_FULL_WINDOW_FLOOR
  - FINITE_NB_TO_GAUSSIAN_HORIZON
  - HALF_WINDOW_VERSUS_FULL_WINDOW_EXPONENT_BOOKKEEPING
OPENS: []
COGNITIVE_OPERATOR: SCALE_AUDIT_AND_RECEIVER_MATCHING
ROUTE_SCORE: 3
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
NUMERICAL_ZERO_SEARCH: NOT_RUN
NUMERICAL_NB_GRID: NOT_RUN
SYMBOLIC_TESTS: EXACT_GAUSSIAN_MOMENTS_AND_RATIONAL_CONSTANT_CHECKS
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
FINAL_COMMIT: REPORTED_IN_DELIVERY_RECEIPT
```

Ы. **RH не доказана.** Доказано строгое количественное ослабление порога R6 C для всей буквальной матрицы и получено сопряжение естественного масштаба для одного достаточного Gaussian-receiver. Это разные результаты: второй не выдаётся за конечную оценку всех направлений.

Главные формулы:

\[
 d_N^2\le e_N\le(\log(2\pi)-\gamma_E)d_N^2;
\tag{R7.1}
\]
\[
 e_N\le m^{-1}\quad\Longrightarrow\quad
 A_m\ge e_N A_m(1/2)-36000(1+\log m)^3G_m;
\tag{R7.2}
\]
\[
 |h_g(t)|\le
 \frac{10^7e^{-35/8}}{(1-e_Nt)^5},
 \qquad 0\le t<e_N^{-1}.
\tag{R7.3}
\]

В частности, при \(N=m\) условие \(e_m\le1/(2\log m)\) даёт постоянный lower bound заранее заданному направлению почти полного разнесения пакетов. Его cofinal версия влечёт RH. Обратная стрелка при \(N=m\) здесь использует RH и точную дополнительную гипотезу Bettin–Conrey–Farmer. Для заранее зарегистрированного
\(N(m)=\lceil\exp((\log m)^3)\rceil\) обратная стрелка следует из RH без дополнительных гипотез.

**Не получено:** глобально оптимальное конечное сопряжение для ВСЕХ \(z\in\mathcal K_m\) с порогом \(1/\operatorname{polylog}m\), безусловный NB-rate и доказательство невозможности всех таких сопряжений. Поэтому полный исход (b) или (c) брифа не объявляется. Оптимальность ниже доказана только для степени в конкретной огибающей C20 и, условно, для порядка \(\log N\) у Gaussian-порога.

## 1. Источники и проверка литературных импортов

[FINITE_CELL | PAPER: source lock и сверка формулировок; не независимый аудит всех прежних доказательств.]

Внутренние короткие пути имеют префикс `docs/routeB_bus/proshka/`.

| Ref | Pin | Использование |
|---|---|---|
| RC | `PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_C.md`, commit `0005623ec3a2b476019899562b50c0854a602dfb`, blob `83004738a32926d80030b52bbae4655ee221dba0` | C1–C32; residue/Mellin dictionary, C12–C22, полная форма и zero-count budgets |
| RB | `PROSHKA_VERDICT_ROUND6_FORWARD_ARROW_2026-11-05_B.md`, commit `888b808094dcc5d8d53686c466f79487ffb1e05f`, blob `33de3e38276671101b701d895509e81d09c0f2e5` | §7.2: точный local factor; собственный planted source и контроль кривой |
| RG | `PROSHKA_VERDICT_PROVE_RH_2026-11-05.md`, commit `62f782316d2ba4f83d27db82d0b64e1e8361cad2`, blob `2b5e02a0aa816da34c204f2a56a9033e6ac6b542` | §§1–6: полный W, фиксированный g, Laplace-полюс, mixed zero formula и literal return |
| R4B | `PROSHKA_VERDICT_ROUND4_DAMPING_TRANSPORT_2026-11-05.md`, commit `dd22692d8db2d880d31d1367b127e315bf50a0dd`, blob `ed2bb7f36eefea3cbcf5c6600741cd72a3acc0d9` | Только доказанный положительный \(Q_m=A_m(1/2)\), не backward flow |
| Intake | Бриф R7 по REQUEST_COMMIT; R6 brief `7db22a05`; addendum C `9dc00979`, blob `b190f1494a4f16faa68e5caaab49abc6b023fc36` | Точный объём задачи |

Freeze записан отдельно до построения. Он не заменён более удобной спецификацией. В нём заранее разделены full-window и Gaussian consumers, \(N=m\) и медленное сопряжение.

**T1 — THEOREM.** Burnol, arXiv:math/0103058v2, Theorem 1.3, печатная p.4. С учётом включения discrete dictionary в continuous dilate class:
\[
 \liminf_{N\to\infty}d_N^2\log N\ge
 B_\zeta:=\sum_{\Re\rho=1/2}^{\rm distinct}m(\rho)^2/|\rho|^2>0.
\]
Это нижняя, не верхняя оценка. Theorem 1.3 и страница проверены визуально.

**T2 — THEOREM WITH RH PREMISE.** Balazard–de Roton, arXiv:0812.1689v1, главный Théorème, p.3:
\[
 RH\Longrightarrow d_N^2\ll_\epsilon
 (\log\log N)^{5/2+\epsilon}/\sqrt{\log N}.
\]
«Без дополнительных гипотез при RH» не означает «безусловно». Проверены PDF и screenshot p.3.

**T3 — THEOREM WITH TWO PREMISES.** Bettin–Conrey–Farmer, arXiv:1211.5191v1, Theorem 1, p.2:
при RH и
\[
 (H_{-1})\qquad
 \exists\delta>0:\quad
 \sum_{|\Im\rho|\le T}|\zeta'(\rho)|^{-2}
 \ll T^{3/2-\delta},
\]
ошибка конкретного
\(V_N(s)=\sum_{n\le N}(1-\log n/\log N)\mu(n)n^{-s}\)
асимптотична \(C_\zeta/\log N\), где
\(C_\zeta=2+\gamma_E-\log(4\pi)\).
Гипотеза \(H_{-1}\) не доказана и подразумевает простоту нулей. Используется как CONDITIONAL supplier, не как THEOREM о настоящем rate. Screenshot p.2 получен по versioned URL после ошибки первого адреса.

**T4 — CONDITIONAL COMPARISON ONLY.** Maier–Rassias, опубликованная версия, Canad. Math. Bull.61 (2018), 622–627, Theorem 1.1, pp.623–624. Кроме ровно одного внеосевого квартета предполагается та же negative-moment гипотеза. Теорема касается ошибки \(V_N\), не оптимального расстояния. В опубликованной формуле есть **и cos, и sin**, в отличие от arXiv v1/формулы брифа. Страница 624 проверена визуально. В наши положительные мосты T4 не импортируется.

Проверка corrections/errata на 2026-11-06: просмотрены указанные arXiv-версии/истории, опубликованный текст MR, запись BCF у издателя/MathNet; выполнены адресные поиски author/title + `erratum`, `corrigendum`, `correction`. Отдельного относящегося к этим четырём результатам erratum не найдено; это ограниченный поиск, не доказательство отсутствия исправлений. Найденное существенное изменение MR между preprint и публикацией учтено. Неаттестованные новые веб-препринты в импорты не включены.

Первичные адреса:
```text
https://arxiv.org/pdf/math/0103058
https://arxiv.org/pdf/0812.1689
https://arxiv.org/pdf/1211.5191v1
https://doi.org/10.1134/S0081543813030036
https://arxiv.org/pdf/1705.09918
https://doi.org/10.4153/CMB-2017-070-3
```

## 2. Точная связь двух NB-остатков

[ABSTRACT / FINITE_CELL | PAPER.]

Пусть \(\rho_n(x)=\{1/(nx)\}\) на \((0,\infty)\),
\(\chi=1_{(0,1)}\), \(\mathscr H=L^2(0,\infty;dx)\). Для
\(A(s)=\sum_{n=1}^Na_nn^{-s}\) положим
\[
 R_A=\chi+\sum_{n=1}^Na_n\rho_n,\qquad
 \mathcal E_N(A)=\|R_A\|_{\mathscr H}^2.
\]
Mellin–Plancherel при \(s=1/2+it\) и
\(\mathcal M\rho_n(s)=-n^{-s}\zeta(s)/s\) дают
\[
 \mathcal E_N(A)=\frac1{2\pi}\int_{\mathbb R}
 |1-\zeta(s)A(s)|^2\frac{dt}{|s|^2}.
\tag{2.1}
\]
Формула \(\mathcal M\rho_n\) следует сначала интегрированием на целых клетках в \(0<\Re s<1\), затем предельным переходом. Это не RH-посылка.

Обозначим \(S_N=\operatorname{span}\{\rho_n-\rho_1/n:2\le n\le N\}\).
На \(x>1\) каждая функция этого пространства равна нулю. RC (C3) отождествляет его с остаточным словарём с весами \(1/[k(k+1)]\). Поэтому **точно**
\[
 e_N=\min_{\substack{A(s)=\sum_{n\le N}a_nn^{-s}\\ A(1)=0}}\mathcal E_N(A),
 \qquad d_N^2=\min_A\mathcal E_N(A).
\tag{2.2}
\]
Знаки: для коэффициентов \(c_n\) residue-словаря
\(A(s)=\sum_{n=2}^Nc_n(1/n-n^{-s})\); действительно \(A(1)=0\).

### Цена центрирования — явная абсолютная константа

На \(x>1\), \(R_A(x)=A(1)/x\). Положим \(b=A(1)\),
\(u=R_A|_{(0,1)}\), \(v=\rho_1|_{(0,1)}\).
Полином \(A^c=A-b\) имеет тот же максимальный индекс N, \(A^c(1)=0\), и
\[
 \mathcal E_N(A^c)=\|u-bv\|^2
 \le(1+\|v\|^2)(\|u\|^2+|b|^2)
 =\kappa\,\mathcal E_N(A).
\tag{2.3}
\]
Здесь
\[
 \kappa=1+\int_0^1\{1/x\}^2dx
       =\log(2\pi)-\gamma_E<2.
\tag{2.4}
\]
Для проверки последнего равенства: после \(y=1/x\), интеграл на \([k,k+1]\) равен
\(1+k/(k+1)-2k\log(1+1/k)\). Сумма до K есть
\(2K+1-H_{K+1}-2K\log(K+1)+2\log(K!)\).
Предел по Stirling равен \(\log(2\pi)-\gamma_E-1\).
Неравенство \(\kappa<2\) следует также сразу из \(0\le v<1\).
Минимизация (2.3) доказывает (R7.1).

Есть и **точная rank-one формула**, не только сравнение.
Пусть \(\Pi_N\) — ортопроекция на \(S_N\),
\(r_N=(I-\Pi_N)\chi\), \(u_N=(I-\Pi_N)\rho_1\). Тогда
\[
 d_N^2=e_N-\frac{|\langle r_N,u_N\rangle|^2}{\|u_N\|^2},
 \qquad \|u_N\|^2\ge1.
\tag{2.5}
\]
Доказательство: \(\operatorname{span}(\rho_1,\ldots,\rho_N)
=S_N+\operatorname{span}\rho_1\), а второй шаг проекции есть одна ортогональная координата \(u_N\). Внешний хвост \(u_N(x)=1/x\) имеет норму 1.

В частности, это не одинаковые остатки:
\(e_1=1\), тогда как
\(d_1^2=1-(1-\gamma_E)^2/\kappa<1\).
RC-контроль \(e_2=1-\log2\) сохраняется.

### Почему \(\log N=L\) не есть изометрия окон

При унитарной логарифмической замене
\((Uf)(y)=e^{-y/2}f(e^{-y})\) функции \(U(S_N)\) живут на всей полуоси \(y\ge0\), не на \([0,\log N]\).
Их fractional-part хвост не исчезает за \(\log N\).
Компактный носитель коэффициентов Dirichlet polynomial в \(\log n\) не есть компактный носитель произведения \(\zeta A_N/s\).
NB-метрика \(|s|^{-2}dt\) также не является Weil-формой с её \(\Gamma,\Lambda\) и полюсами. Равенство длин само по себе не даёт ни Gram-равенства, ни оплаченного дефекта.

## 3. Полная буквальная матрица: порог \(m^{-6}\) ослаблен до \(m^{-1}\)

[FINITE_CELL | PAPER; исходная огибающая RC C20, её новая оптимизация.]

Пишем \(L=\log m>1\), \(Q_m=A_m(1/2)\), \(P_{m,N}=e_NQ_m\).
Для каждого \(m\ge3,N\ge1,T\ge1\) RC даёт
\[
 A_m\ge P_{m,N}-[D(e_N,L,T)+64(1+L)e_N]G_m,
\tag{3.1}
\]
\[
 D(e,L,T)=10800L^2a\,e^{La}
       +1728L\sqrt m\,\frac{\log(T+2)}T,\quad
 a=\min\{1/2,e(1+T^2)/2\}.
\tag{3.2}
\]
Здесь сохранены обе границы физического окна и **полная** mixed explicit formula; не производится новое удаление \(\Gamma\), полюса или prime powers.

**Теорема 1.** Для всех указанных m,N и всех \(z\in\mathbb C^{m+1}\):
\[
 e_N\le\frac1{mL}
 \Longrightarrow A_m\ge P_{m,N}-36000(1+L)^2G_m;
\tag{3.3}
\]
\[
 e_N\le\frac1m
 \Longrightarrow A_m\ge P_{m,N}-36000(1+L)^3G_m.
\tag{3.4}
\]

**Доказательство (3.3).** Берём \(T=\sqrt m\).
Тогда \(aL\le(1+m)/(2m)\le2/3<1\), \(e^{La}<3\);
первый член не больше \(32400L\).
Из \(\sqrt m+2\le3\sqrt m\) и \(L\ge\log3\)
второй не больше \(2592L^2\).
Остаток положительного выхода не больше \(64(1+L)\).
Их сумма меньше \(36000(1+L)^2\).

**Доказательство (3.4).** Берём \(T=\sqrt{m/L}\ge1\).
Теперь \(aL\le(1+L/m)/2\le1\).
Первый член опять не больше \(32400L\), второй — не больше
\(2592L^{5/2}\), последний — \(64(1+L)\).
Сумма меньше \(36000(1+L)^3\). □

Это конечные импликации на **всех** направлениях, следовательно и на \(\mathcal K_m\). Они строго слабее прежнего требования \(e_N\le m^{-6}\). Получение такого e_N без RH здесь не утверждается.

### 3.1. Критическая степень в C20 ровно 1 — но только в C20

[COFINAL_FAMILY | PAPER.]

Пусть при фиксированных \(C>0,r\ge0\) какой-либо выбор \(T=T(m)\ge1\) обеспечивает
\(D(e,L,T)\le C(1+L)^r\).
Для достаточно больших L хвост заставляет
\[
 T\ge\frac{1728\log3}{C}\frac{L\sqrt m}{(1+L)^r},
 \quad \log T\ge L/3,\quad
 T\ge\frac{576}{C}\frac{L^2\sqrt m}{(1+L)^r}.
\]
Насыщение \(a=1/2\) невозможно: первый член тогда \(5400L^2\sqrt m\).
Для \(x=La\) имеем
\(xe^x\le C(1+L)^r/(10800L)\), откуда
\[
 e\le
 \frac{C^2(1+L)^{2r}}{165888\,mL^5}
 \left[1+\log_+\frac{C(1+L)^r}{10800L}\right].
\tag{3.5}
\]
Все утверждения справедливы, как только выполнены явные условия
\[
 \frac L6+\log\!\left(\frac{1728\log3}{C}\frac L{(1+L)^r}\right)\ge0,
 \qquad 5400L^2\sqrt m>C(1+L)^r.
\]
Они выполнены при всех достаточно больших L. Таким образом цена C20 требует
\(e\le m^{-1+o(1)}\); (3.4) достигает критической степени 1.

**Это не lower bound отрицательности A_m.** Большая цена достаточной огибающей не опровергает меньший настоящий defect. (3.5) запрещает получить inverse-polylog порог одной оптимизацией T в C20, но не запрещает иной source-specific мост.

T1 и (R7.1) означают: для достижения \(e_N\le1/m\) необходимо
\(\log N\ge(B_\zeta-o(1))m\).
Экспоненциальная цена этого сертификата уменьшена с \(\exp(c m^6)\) до масштаба \(\exp(c m)\), но не до \(\exp(\operatorname{polylog}m)\).

## 4. Новый конечный мост: NB-ошибка задаёт временной горизонт Gaussian

[FINITE_CELL / ABSTRACT | PAPER.]

Используем **тот же** профиль RG:
\[
 g(x)=\pi^{-1/2}(16x^4-49x^2+25/2)e^{-x^2},\qquad
 F(u)=u^2(u^2-1/4)e^{u^2/4}.
\]
Положим \(h_g(t)=W(g,T_tg)\), \(t\ge0\). Полная, безусловная mixed formula:
\[
 h_g(t)=\sum_\rho F(\rho-1/2)^2e^{(\rho-1/2)t}.
\tag{4.1}
\]
Комплексные квадраты не заменяются модулями в равенстве.

Для любого настоящего нуля \(\rho=\beta+i\gamma\) RC C12 и точная функциональная симметрия дают
\[
 |\beta-1/2|\le \frac{e_N}{2}(1+\gamma^2).
\tag{4.2}
\]
Отдельно используется известный strip \(|\beta-1/2|<1/2\).
Кратности включены в
\(\Sigma_0=\sum_\rho(1+\gamma^2)^{-1}\le100\), RC C14.
Это не вычисленная таблица нулей.

**Теорема 2 (конечный горизонт).** Для каждого конечного N и каждого \(t\ge0\) с \(e_Nt<1\) выполнено (R7.3), где
\[
 K_0=10^7e^{-35/8}<128206.
\tag{4.3}
\]

**Доказательство.** Положим \(a=\beta-1/2\), \(X=\gamma^2\).
При \(|a|\le1/2\)
\[
 |F(a+i\gamma)|^2\le(1+X)^4e^{1/8-X/2}.
\]
Пусть \(q=1-e_Nt\in(0,1]\).
Из (4.2), абсолютной сходимости (4.1) и \(\Sigma_0\le100\):
\[
 |h_g(t)|
 \le100e^{1/8+e_Nt/2}
       \sup_{X\ge0}(1+X)^5e^{-qX/2}.
\]
Максимум достигается при \(X=10/q-1\) и равен
\((10/q)^5e^{-5+q/2}\).
Поскольку \(e_Nt+q=1\), получаем ровно \(K_0q^{-5}\). □

Для фиксированного положительного запаса \(1-e_Nt\ge1/2\):
\[
 |h_g(0)|\le K_0,\qquad |h_g(t)|\le32K_0.
\tag{4.4}
\]
Это quantitative finite assertion, а не только \(e_N\to0\).
Причина естественного \(\log N\leftrightarrow\log m\) — горизонт \(t\lesssim1/e_N\) при ожидаемом \(e_N\asymp1/\log N\), **не** мнимое совпадение носителей Hilbert-пространств.

## 5. Возврат в буквальное окно с явно определённой ценой ошибок

[ABSTRACT / FINITE_CELL | PAPER.]

Чтобы не спрятать новое сопряжение в неопределённом \(O(1)\), зададим source-норму. Для функций, для которых правая часть конечна, положим
\[
 S(f)=\|e^{|x|}f\|_2,\quad
 J(f)=\int_0^\infty j(u)\|f-T_uf\|_2^2du,\quad
 \mathfrak B(f)^2=J(f)+21S(f)^2,
 \quad j(u)=\frac{e^{-u/2}}{1-e^{-2u}}.
\tag{5.1}
\]
Для полного источника W из RG, с обеими полюсными координатами,
\[
 |W(f,k)|\le\mathfrak B(f)\mathfrak B(k).
\tag{5.2}
\]

**Доказательство всех констант.** Archimedean jump-часть ограничена \(\sqrt{J(f)J(k)}\).
Контактная константа \(c_*=\gamma_E+\log(8\pi)+\pi/2<6\).
Неравенство \(|x|+|x-u|\ge|u|\) даёт
\[
 |\langle f,T_uk\rangle|\le e^{-|u|}S(f)S(k).
\]
По \(\Lambda(n)\le\log n\) и сравнению на \([n-1,n]\):
\[
 \sum_{n\ge2}\Lambda(n)n^{-3/2}
 \le\int_1^\infty(\log x+\log2)x^{-3/2}dx
 =4+2\log2<6.
\]
Две prime-суммы стоят не больше \(12S(f)S(k)\).
Каждый момент \(M_\pm(f)=\int f(x)e^{\pm x/2}dx\) удовлетворяет
\(|M_\pm(f)|\le\sqrt{4/3}\,S(f)\); обе смешанные полюсные части стоят \(8S(f)S(k)/3\).
Итого \(6+12+8/3<21\). Последний переход к (5.2) — Cauchy–Schwarz в двух координатах. Никакая неизвестная prime-error оценка здесь не используется. □

При \(L=\log m\) и любом выбранном ниже разнесении \(t=t_m\) зададим
\[
 v_m(x)=g(x-t/2)+g(x+t/2).
\]
Пусть \(\chi_m\) — явно заданный чётный smooth cutoff в \(I_L\).
Разложим \(\chi_m v_m\) в исходном базисе
\[
 \phi_j(x)=d_j(-1)^j\cos(2\pi jx/L)/\sqrt L,\quad
 d_0=1,\ d_j=\sqrt2\ (j\ge1),\quad 0\le j\le m.
\]
Обозначим его коэффициенты \(v_{m,j}\), положим
\[
 \widetilde v_m=v_m^{\rm coeff}-v_{m,0}e_0,\qquad
 w_m=\widetilde v_m-\frac{p_m^*\widetilde v_m}{p_{m,1}}e_1,
 \qquad f_m=\mathcal S_m w_m.
\tag{5.3}
\]
Здесь \(p(x)=\sqrt2\cosh(x/2)\), \(p_m=\mathcal S_m^*p\), и ТОЧНО
\[
 p_{m,1}=\frac{2\sinh(L/4)}
 {\sqrt L\,\{1/4+(2\pi/L)^2\}}>0.
\tag{5.4}
\]
Следовательно \(w_m\in\mathcal K_m\) без приближённого зануления моментов.

Все объекты в следующем бюджете определены без нулей и без знака A:
\[
 D_m=w_m^*G_mw_m,\quad r_m=f_m-v_m,\quad
 \epsilon_m=\mathfrak B(r_m)
                    [\,2\mathfrak B(v_m)+\mathfrak B(r_m)\,].
\tag{5.5}
\]
Обе границы окна входят в \(J(r_m)\); нулевое продолжение f_m не объявляется H¹-функцией.
Трансляционная инвариантность полного W и (5.2) дают
\[
 |w_m^*A_mw_m-2h_g(0)-2h_g(t_m)|\le\epsilon_m.
\tag{5.6}
\]
В частности, если \(D_m>0\) и \(e_Nt_m<1\), то для \(z_m=w_m/\sqrt{D_m}\)
\[
 z_m^*A_mz_m\ge-
 \frac{2K_0\{1+(1-e_Nt_m)^{-5}\}+\epsilon_m}{D_m}.
\tag{5.7}
\]
Это **явная finite bridge inequality**; все её константы указаны. \(\epsilon_m,D_m\) — определённые нормы известных функций, не подставленная оценка неизвестного A_m.

Точный расчёт Gaussian-моментов даёт
\[
 E_g:=\|g\|_2^2+\|g'\|_2^2
 =\frac{8889}{8\sqrt{2\pi}}>440,
\quad
 \|g\|_2^2=\frac{1803}{16\sqrt{2\pi}},
\quad
 \|g'\|_2^2=\frac{15975}{16\sqrt{2\pi}}.
\tag{5.8}
\]
При трёх проверяемых условиях
\[
 e_Nt_m\le\frac12,\qquad \epsilon_m\le1,\qquad D_m\ge E_g
\tag{5.9}
\]
получаем
\[
 z_m^*A_mz_m\ge-20000.
\tag{5.10}
\]
Действительно \(K_0<10^7/78\), поскольку
\(\sum_{j=0}^{10}(35/8)^j/j!>78\), и
\((66\cdot10^7/78+1)/440<20000\).

Если дополнительно \(e_N L\le1\), то RC C21 и \(z_m^*G_mz_m=1\) дают
\[
 z_m^*A_mz_m\ge z_m^*P_{m,N}z_m-20200,
 \qquad P_{m,N}=e_NA_m(1/2)\ge0.
\tag{5.11}
\]
Добавочная цена не больше \(64(1+L)e_N\le128\) при \(L\ge1\).
Это scalar output inequality на одном указанном z_m, НЕ операторное неравенство на всей \(\mathcal K_m\).

## 6. Почти полное разнесение: показатель \(\Theta\), а не \(\Theta/2\)

[COFINAL_FAMILY | PAPER. Новое семейство, не задняя правка RG.]

В RG центры находились в \(\pm L/4\), расстояние было \(t=L/2\).
Поэтому его показатель действительно \(\Theta/2\). Чтобы сравнивать с повреждением порядка \(m^{a+o(1)}\), строим другое, заранее разрешённое во freeze семейство.

Для \(L\ge4096\) положим
\[
 d=L^{3/4},\qquad t_m=L-2d,\qquad
 x_\pm=\pm(L/2-d).
\tag{6.1}
\]
Зафиксируем \(b(u)=e^{-1/u}\) при \(u>0\), \(b(u)=0\) иначе,
\(s(u)=b(u)/(b(u)+b(1-u))\), и
\[
 \chi_m(x)=1-s\left(
 \frac{|x|-(L/2-d/2)}{d/2}\right).
\tag{6.2}
\]
Она равна 1 при \(|x|\le L/2-d/2\) и 0 при \(|x|\ge L/2\); возле x=0 постоянна.
Далее применяем буквально (5.3). Зависимости от нулей или eigenvectors A_m нет.

### Оплата cutoff, проекции и двух моментов

Расстояние центров до начала перехода cutoff равно \(d/2\).
Поэтому для каждого фиксированного A,j ошибка cutoff с весом \(e^{A|x|}\) ограничена полиномом по L,d, умноженным на
\[
 \exp[-c_j d^2+O_A(L)]
 =\exp[-c_j L^{3/2}+O_A(L)].
\tag{6.3}
\]
Здесь c_j>0 — обычная Gaussian tail-константа; для конечных оценок вместо асимптотики используется ТОЧНО (5.5). Ни коэффициент, ни остаток не зависят от нулей.

Срезанная функция имеет все нулевые краевые производные. Для любого фиксированного порядка q её внутренние Sobolev-нормы ограничены равномерно при больших L: это две трансляции одного g и cutoff, чьи производные дают степени \(d^{-1}\).
Cosine/Fourier tail после частоты \(2\pi m/L\) поэтому убывает как любая выбранная степень m с логарифмическим множителем. Умножение на вес \(e^{|x|}\) внутри окна стоит не больше \(m^{1/2}\).

Для любого h на I_L с внутренней H¹-нормой конечной, прямое разделение u≤1/u≥1 даёт
\[
 J(h_{\rm zero\ extended})\le16
       (\|h\|_2^2+\|h'_{\rm int}\|_2^2),\qquad L\ge1.
\]
При u≤1 учитываются два краевых отрезка:
\(\|h-T_uh\|^2\le u^2\|h'_{\rm int}\|^2+2u\|h\|_\infty^2\),
\(\|h\|_\infty^2\le2(\|h\|^2+\|h'_{\rm int}\|^2)\).
Это оплачивает скачки cosine-tail, не скрывает их.

Для полного v_m средний и оба полюсных момента точно нулевые, поскольку \(F(0)=F(1/2)=F(-1/2)=0\).
Следовательно поправки (5.3) зависят только от уже малых ошибок cutoff/projection. Цена \(p_m\), \(1/p_{m,1}\) и веса на окне — не более полиномиальной по m, по (5.4).
Итак, для каждого B>0
\[
 \mathfrak B(r_m)=O_B(m^{-B}),\quad
 \epsilon_m=O_B(m^{-B}),\quad
 D_m\longrightarrow2E_g.
\tag{6.4}
\]
Последний предел использует исчезающее перекрытие двух разнесённых Gaussian.
Конкретное численное \(m_0\) для (5.9) не вычислено: для finite-cell применения проверяются явные (5.5),(5.9). Для cofinal вывода существование m_0 доказано (6.4).

### Теорема 3: исходный показатель потерь восстановлен

Пусть
\(\Theta=\sup_{\xi(\rho)=0}|\Re\rho-1/2|\).
Для \(z_m\), построенных в (5.3),(6.1)–(6.2),
\[
 \limsup_{m\to\infty}
 \frac{\log(1+(-z_m^*A_mz_m)_+)}{\log m}=\Theta.
\tag{6.5}
\]
При \(\Theta>0\), для каждого \(0\le b<\Theta\),
\[
 \liminf_{m\to\infty}\frac{z_m^*A_mz_m}{m^b}=-\infty.
\tag{6.6}
\]

**Доказательство.** RG §§4–5 даёт для h_g(t) верхнюю экспоненту \(\Theta\) и отрицательные осцилляции с каждым показателем c<Θ; это следует из ненулевого Laplace-вычета \(F(\rho-1/2)^2\), а не из расположения предполагаемых нулей на линии.
Здесь \(t_m/L\to1\), поэтому из (5.6),(6.4) получается верхняя оценка (6.5).
Для нижней выбираем b<c<Θ.
Для любого большого t существует ближайшее целое m к решению \(t=\log m-2(\log m)^{3/4}\).
Производная правой части по m равна
\(m^{-1}[1-\tfrac32(\log m)^{-1/4}]\); поэтому \(|t-t_m|=O(m^{-1})\).
Из полной Gaussian-суммы \(|h_g'(t)|\le C_g e^{t/2}\).
Ошибка округления, следовательно, \(O(m^{-1/2})\).
Осцилляции \(h_g(t)\le-Ke^{ct}\) переживают округление, а
\(e^{ct_m}/m^b=\exp[(c-b)L-2cL^{3/4}]\to\infty\).
Нормировка D_m имеет положительный конечный предел и не меняет показатель. □

Отсюда одна достаточная, но НЕ доказанная для настоящей арифметики посылка:
\[
 \forall\text{ достаточно больших }m:\quad
 e_{N(m)}\le\frac1{2\log m}
 \quad\Longrightarrow\quad
 z_m^*A_mz_m\ge-20000\quad\Longrightarrow\quad RH.
\tag{6.7}
\]
Первый переход использует \(t_m\le L\), (5.7)–(6.4).
Второй — (6.6), либо тот же Laplace-полюсный механизм RG.
Требуются **все поздние m**, не выбранная хорошая подпоследовательность.

## 7. Сопряжения и точные остаточные леммы

[COFINAL_FAMILY | PAPER для импликаций; CONDITIONAL для неподтверждённых арифметических посылок.]

### 7.1. Основной кандидат \(N=m\)

Искомая строка:
\[
 (\mathrm{R}_{\rm fast})\qquad
 \exists M\ \forall m\ge M:\quad e_m\le\frac1{2\log m}.
\tag{7.1}
\]
Доказано
\[
 (\mathrm{R}_{\rm fast})\Longrightarrow RH.
\tag{7.2}
\]
В обратную сторону T3 и (2.3) дают
\[
 RH+H_{-1}\Longrightarrow
 \limsup_{N\to\infty}e_N\log N
 \le\kappa C_\zeta<\tfrac12
 \Longrightarrow(\mathrm{R}_{\rm fast}).
\tag{7.3}
\]
Для строгого \(\kappa C_\zeta<1/2\) достаточно элементарных
\(\kappa<2,\ \gamma_E<3/5,\ \log(4\pi)>5/2\);
тогда \(C_\zeta<1/10\).
Ни RH=>\(H_{-1}\), ни RH=>\(\mathrm R_{\rm fast}\) без дополнительного входа здесь не доказаны.

Условно на H_{-1} это обе нужные стрелки. Безусловно установлена только прямая достаточность (7.2). Слово «мягкая» в описании H_{-1} не превращает её в теорему.

### 7.2. Зарегистрированное медленное сопряжение без дополнительных гипотез

Положим \(N_*(m)=\lceil\exp((\log m)^3)\rceil\) и
\[
 (\mathrm{R}_{\rm slow})\qquad
 \exists M\ \forall m\ge M:\quad
 e_{N_*(m)}\le\frac1{2\log m}.
\tag{7.4}
\]
Тогда
\[
 \boxed{\,(\mathrm{R}_{\rm slow})\ \Longleftrightarrow\ RH\,}.
\tag{7.5}
\]
Вперёд — (6.7). Назад — T2 при \(\epsilon=1/4\), (R7.1) и
\[
 L e_{N_*(m)}
 \ll \frac{(3\log L)^{11/4}}{\sqrt L}\longrightarrow0.
\tag{7.6}
\]
Скрытая константа здесь принадлежит литературной **RH-условной** оценке T2; она не используется в finite bridge (5.7). Условие существования достаточно большого M не выдаётся за вычисленный stopping index.

Это действительно \(N\le\exp(\operatorname{polylog}m)\).
Но неизвестность (7.4) без RH не устранена: (7.5) классифицирует силу леммы, не доказывает её.

### 7.3. Что здесь оптимально, а что нет

Burnol и \(d_N^2\le e_N\) показывают: достижение порога \(e_{N(m)}\le1/(2L)\) требует
\[
 \log N(m)\ge(2B_\zeta-o(1))L.
\tag{7.7}
\]
Поэтому порядок \(\log N\asymp L\) оптимален **по масштабу для этого порога**, если верхняя скорость T3 разрешена; N=m тогда подходит. Не заявляется оптимальная константа сопряжения.

Полная цепочка:
\[
 \mathrm R_{\rm fast}\ \text{или}\ \mathrm R_{\rm slow}
 \ \Longrightarrow\ \text{равномерный scalar lower bound (5.10)}
 \ \Longrightarrow\ RH
 \ \Longrightarrow\ A_m\succeq0\ \text{для каждого }m.
\tag{7.8}
\]
Последняя стрелка — исходная полная явная формула при RH.
Она **глобальная**. Из неё запрещено делать вид, будто одна проверка e_N при одном m уже доказала PSD всего A_m.

Поэтому полный finite-cell порог \(1/\operatorname{polylog}m\) на всех \(\mathcal K_m\), требуемый задачей 1, остаётся OPEN. Для него безусловный новый результат — (3.4), а не (7.8).

### 7.4. Попытка оплатить rate явным \(V_N\): точный head, неоплаченная норма

[FINITE_CELL | PAPER для тождеств; COFINAL_FAMILY | CONDITIONAL для малости.]

Пусть \(a_n=\mu(n)(1-\log n/\log N)\), \(N\ge2\),
\(b_N=V_N(1)=\sum_{n\le N}a_n/n\).
Центрированный полином \(V_N-b_N\) соответствует остаткам
\[
 R_N^V(k)=1+\sum_{n=2}^Na_n r_n(k)
         =1+kb_N-\sum_{n\le N}a_n\lfloor k/n\rfloor .
\tag{7.9}
\]
Из точных целочисленных тождеств
\(\sum_{d\mid j}\mu(d)=1_{j=1}\) и
\(\sum_{d\mid j}\mu(d)\log d=-\Lambda(j)\) следует
\[
 R_N^V(k)=kb_N-\frac{\psi(k)}{\log N},\qquad 1\le k\le N.
\tag{7.10}
\]
При k>N добавляется ровно
\[
 \sum_{N<n\le k}\mu(n)
       (1-\log n/\log N)\lfloor k/n\rfloor.
\tag{7.11}
\]
Ни \(\psi-x\), ни нули не являются входом коэффициентов a_n; \(\psi\) здесь появляется как **проверяемый выход** целочисленного divisor-identity.
Все степени простых сохранены.

Конечное неравенство
\[
 e_N\le\sum_{k\ge1}\frac{|R_N^V(k)|^2}{k(k+1)}
      =\mathcal E_N(V_N-b_N)\le\kappa\mathcal E_N(V_N)
\tag{7.12}
\]
доказано. Но безусловный bound этой полной суммы величиной \(1/(2\log N)\) не получен.
Правильный head и абсолютная PNT-оценка не оплачивают квадратную норму с хвостом (7.11). Оптимальный e_N может быть лучше этого V_N; провал оценки выбранного полинома не опровергает rate оптимального словаря.
Таким образом открытая строка не исчезла после выбора taper; она осталась количественной задачей совместной нормы.

## 8. Дискриминатор: что именно имеет показатель \(2a\), \(a\), \(a/2\)

[ABSTRACT / COFINAL_FAMILY | PAPER для аудита величин; T4 — только CONDITIONAL comparison.]

Для внеосевого смещения \(a=\sigma_0-1/2>0\) опубликованная формула MR имеет вид
\[
 \mathcal E_N(V_N)=\frac{N^{2a}}{\log^2N}
 [A\cos(2\gamma_0\log N)+B\sin(2\gamma_0\log N)+C]\,
 [1+O(N^{-a+\varepsilon})].
\tag{8.1}
\]
Применимость требует собственных посылок T4. Фазовый коэффициент может осциллировать; сравнение показателей ниже не утверждает равномерную положительную нижнюю границу этого коэффициента.

**Оптимальные расстояния — другие величины:**
\[
 0\le d_N^2\le e_N\le1
\tag{8.2}
\]
для каждого N: в минимизации доступен нулевой аппроксимант.
Поэтому требование \(e_N\ge cN^{2a}/\log^2N\) на неограниченной последовательности, c>0, невозможно. Для такого требования строгая верхняя огибающая разности равна
\[
 e_N-cN^{2a}/\log^2N\le1-cN^{2a}/\log^2N<0
\]
при достаточно большом N. Это точный `KILL_THEOREM_SHAPE` переноса роста **явного** V_N на **infimum**, не опровержение MR, N=m или NB-критерия.

Если \(N=m^\kappa\) и физическое разнесение \(t=\theta L+o(L)\), то:

| Величина | Степенной масштаб внеосевого вклада |
|---|---|
| \(\mathcal E_N(V_N)\), квадрат нормы | \(m^{2a\kappa}\) с log-знаменателем |
| \(\sqrt{\mathcal E_N(V_N)}\), норма | \(m^{a\kappa}\) с log-знаменателем |
| \(h_g(t)\), линейный translated response | \(m^{a\theta+o(1)}\) |
| Старый RG receiver | \(\theta=1/2\), показатель \(a/2\) |
| Новый receiver §6 | \(\theta=1\), показатель a |

Следовательно N=m согласуется по показателю с **нормой**, не её квадратом, для нового near-edge receiver.
Для старого receiver сопоставление с нормой потребовало бы \(N=m^{1/2}\); сопоставление с квадратом — \(N=m^{1/4}\).
Для нового receiver сопоставление с квадратом потребовало бы \(N=m^{1/2}\).

Это точная арифметика показателей, **не доказательство равенства двух норм**.
FATAL для буквального отождествления «\(e_m\) растёт как \(m^{2a}\), потому что MR» локализован в (8.2).
Исправление не скрыто: для output-receiver изменено физическое расстояние с полностью оплаченной границей; оптимальный e_N не переименован в ошибку V_N.

### 8.1. Настоящий planted source из R6 B

RB строит
\[
 \xi_{\rm pl}(s)=Q(s-1/2)\xi(s)/Q(1/2),
 \qquad Q(w)=((w-a)^2+\gamma^2)((w+a)^2+\gamma^2).
\]
При размещении Q в archimedean Mellin-факторе **ζ и обычный e_N не меняются**.
Требовать для такого e_N формулу (8.1) — source mismatch.
Новый квартет не является нулями ζ, поэтому RC C12 и (4.2) не применяются к нему.

Для ПОЛНОГО источника plant присутствует добавка Q'/Q и ядро
\(4\cosh(au)\cos(\gamma u)\).
Её четыре моментных члена ограничены \(16S(f)S(k)/3\), поэтому в (5.1) достаточно заменить 21 на 27. Ошибки near-edge возврата опять сверхполиномиальны.
Ненулевые вычеты в точках \(u=\pm a\pm i\gamma\), включая случай совпадения с прежним нулём, дают
\[
 \liminf_m\frac{z_m^*A_m^{\rm pl}z_m}{m^b}=-\infty
 \quad\text{для каждого }0\le b<a.
\tag{8.3}
\]
Использован собственный полный источник и Laplace-Landau аргумент RG/RB, не предположение RH для исходной ξ.
Для a=1/3 это отрицательные показатели вплоть до 1/3, а не 1/6 старого разнесения.

Если перенести Q из Gamma в незавершённый фактор \(Z=Q\zeta/Q(1/2)\), обычный residue-dictionary перестанет иметь нужную Mellin-идентичность; коэффициенты \(\mu(n)\) не являются автоматически обратными коэффициентами Z.
Если источник-корректный L²-словарь вообще построен и зануляется в planted \(\rho\), то его целевой остаток имеет постоянную нижнюю границу
\((2\Re\rho-1)/|\rho|^2\).
Нельзя одновременно сохранить этот link и получить inverse-log capture.

## 9. Точный local factor и остальные миры

[ABSTRACT / COFINAL_FAMILY | PAPER с указанными source imports.]

**Где входит настоящий Γ.** Обычное целочисленное деление даёт
\(\mathcal M(Jr_n)=(1/n-n^{-s})\zeta(s)/s\).
Переход от его нулей к отражённым парам и к **полной** W-форме использует именно
\[
 \xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
\tag{9.1}
\]
В критической полосе Gamma не имеет нулей; нет дополнительных Q-нулей, невидимых residue-dictionary. Это link (4.2) → (4.1) и одновременно C17 в full-window мосте.
Gamma/pole/source terms не отбрасываются: их полный учёт содержится в mixed formula и проверяется независимой bound (5.2).
Положительность seed и Poisson не заменяют (9.1), как точно показал RB §7.2.

**DMV.** r_n(k) и интервалы \((1/(k+1),1/k]\) используют соседние обычные целые. Их Mellin-transform вычисляет ζ, не generalized zeta_B.
Ломается additive source-match уже до (4.2).
Для гипотетического source-correct L²-словаря, зануляющегося в одном правом \(\rho_B\), Cauchy–Schwarz даёт
\[
 e_N^B\ge (2\Re\rho_B-1)/|\rho_B|^2>0
\]
при каждом N; порог \(1/(2L)\) не проходит cofinal тест.
Отражённое completion и положительный terminal DMV не выдумываются.

**DH.** Требуется его собственный uncompleted D, odd-Gamma и все коэффициенты; обычная Mellin-идентичность r_n с ζ не является такой идентичностью для D.
При любом существующем L² Mellin-null ремонте правый DH-нуль даёт ту же постоянную evaluation barrier.
Это отказ source-match/capture, не отказ универсальной положительности Gram.

**Кривая над \(\mathbb F_3\).** Для её собственного источника h=log3:
\[
 (Rf)(x)=\sum_{k\in\mathbb Z}(-1)^kf(x+2hk),\quad0\le x<2h,
 \qquad A_m^E[f]=2h\|Rf\|_2^2\ge0.
\tag{9.2}
\]
Это конгруэнция положительной метрики, точная на каждом буквальном окне, с defect 0; endpoint shifts имеют нулевое перекрытие.
Собственный полиномиальный NB-аналог тоже проходит rate-проверку. При \(P(z)=1+z^2\), \(z=e^{-h(s-1/2)}\), зададим
\[
 U_M(z)=\sum_{k=0}^M(-1)^k(1-k/(M+1))z^{2k}.
\]
Прямое умножение даёт
\[
 1-P(z)U_M(z)=\frac1{M+1}
             \sum_{k=1}^{M+1}(-1)^kz^{2k},
 \qquad
 \|1-PU_M\|_{L^2(\mathbb T,d\theta/2\pi)}^2=\frac1{M+1}.
\tag{9.3}
\]
Положительная ортогональность Fourier-мономов платит точную норму.
При M=m она меньше \(1/(2\log m)\) для всех m≥3.
Это собственные dictionary, метрика и фактор кривой, не подмена её обычным ζ-словарём.

**Taper не равен damping.** Вес \((1-u/\log N)_+\) и \(e^{-\delta u}\) различны на внутренности окна. При \(\delta=c/L\), u=L первый нулевой, второй \(e^{-c}\); нулевое перекрытие Q_f(L) не обнуляет разность для 0<u<L.
Точное paid тождество переноса между ними здесь не предъявлено. Положительность каждого kernel отдельно не разрешает вычесть их разность бесплатно.

## 10. Strongest attack, проверки и судьба предсказаний

[ABSTRACT / FINITE_CELL | PAPER.]

**Сильнейшая атака на собственный результат:** scalar Gaussian bound не является full-matrix bound. Она отражена в (5.11),(7.8), а не спрятана за словами «natural coupling».
Вторая атака — near-edge пакеты могут выходить из буквального carrier; это оплачено (5.1)–(6.4), включая оба скачка края, проекцию N=m и точное зануление двух моментов.
Третья — невидимый quartet при неизменном обычном e_N; это реальный source-match разрыв §8.1, а не доказанное универсальное обнаружение по одной NB-норме.

| Prediction | Fate |
|---|---|
| P1, constraint/centering | HIT: (2.2)–(2.5), точная \(\kappa\) |
| P2, weaker whole-window threshold | HIT AND STRENGTHENED: достигнуто e≤1/m; оптимальность только внутри C20 |
| P3, Gaussian eL-budget | HIT: конечная (5.7), constant floor (5.10) |
| P4, MR vs infimum/plant | HIT: bounded infimum, published sin-term, exact source mismatch |
| P5, same-length ≠ same space | HIT: half-line Mellin-tail |
| P6, reverse implications | HIT WITH STATED PREMISES: fast требует H_-1; slow — только RH |

Выполнены точные Gaussian-moment и rational-constant проверки стандартной символьной арифметикой. Также проверено divisor-log тождество на зарегистрированных малых индексах; доказательство (7.10) дано для всех k, не выводится из этих проверок.
Ни NB-grid, ни numerical zero-search, ни собственные значения A_m не вычислялись.
Lean, Arb и независимый аналитический аудит не выполнялись.

Воспроизводимая точная проверка чисел (Python + SymPy):
```python
import math
from fractions import Fraction
import sympy as sp

x = sp.symbols("x")
p = 16*x**4 - 49*x**2 + sp.Rational(25, 2)
dp = sp.diff(p, x) - 2*x*p

# Integral x^(2j) exp(-2 x^2)/pi dx
# equals (2j-1)!! / (4^j sqrt(2*pi)).
def moment_coefficient(poly):
    return sp.simplify(sum(
        c * sp.factorial2(k-1) / 4**(k//2)
        for (k,), c in sp.Poly(sp.expand(poly), x).terms()
        if k % 2 == 0
    ))

assert moment_coefficient(p*p) == sp.Rational(1803, 16)
assert moment_coefficient(dp*dp) == sp.Rational(15975, 16)
assert sum(Fraction(35, 8)**j / math.factorial(j)
           for j in range(11)) > 78
assert (66*Fraction(10**7, 78) + 1)/440 < 20000
# Using the classical bound pi < 22/7 also certifies E_g > 440.
assert Fraction(8889, 8*440)**2 > Fraction(44, 7)
```
Переменная x — физическая координата; p — polynomial part g; dp — polynomial part g′. Подстановок пользовательских параметров не требуется. Проверка не вызывает ζ, zero tables или A_m.

**Finite falsifiers остаются теми, что закреплены во freeze.** Более сильный all-direction порог e≤1/(2L) не объявлен теоремой и не прошёл grid. Перед попыткой его вычислительного доказательства нужны interval-tail bounds и plant; обычные 80/120-digit совпадения — только DIAG.
Zero-consistent результат различается точной constraint A(1)=0, полной source identity (9.1) либо ненулевым Laplace-вычетом, а не бесконечным повышением precision.

## 11. Dependency epistemics и следующие две репрезентации

[COFINAL_FAMILY | CONDITIONAL для открытых поставщиков.]

**K8A — незакрытый полный consumer.**
DOWNSTREAM_CONSUMER: RH, затем полный literal Weil sign.
ACTUAL_CONSUMER_REQUIREMENT: достаточно cofinal lower bound одного source-independent near-edge Gaussian; весь finite-cell floor — дополнительная обязанность брифа.
ORIGINAL_REQUESTED_OBJECT: optimal one-cell NB-to-whole-window bridge при N≤exp(polylog m).
ORIGINAL_OBJECT_IS: UNKNOWN как необходимый для RH; не объявлен обязательным.
KNOWN_WEAKER_INTERFACES: (5.7)+(7.1) или (7.4) => (6.7) => RH; RC C20 с улучшением (3.4) даёт другой полный consumer.
FAILURE_TYPE: NO_DERIVATION.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: finite threshold/horizon, centering constant, paid near-edge exponent.
REOPEN_TRIGGER: новое физически спаренное NB-to-Weil неравенство, которое контролирует все K_m без промежуточного cofinal RH; либо безусловный supplier для (7.1)/(7.4).

**K8A — единственный kill.**
ORIGINAL_REQUESTED_OBJECT: положительный степенной MR-growth, приписанный оптимальному e_N.
ORIGINAL_OBJECT_IS: NOT_NECESSARY.
KILL_SCOPE: THEOREM_SHAPE.
KILL_EVIDENCE_KIND: strict upper envelope (8.2), section 8 этого файла.
FAILURE_TYPE: COUNTEREXAMPLE.
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD только для названного отождествления.
REOPEN_TRIGGER: заменить объект на настоящий \(\mathcal E_N(V_N)\), явно сохранив square/root и source. Это другая корректная задача, не ремонт ложного равенства.
Теорема MR, actual N=m и вся NB-family не убиты.

**Две остающиеся репрезентации.**

A. **Физически спаренный Hardy/Mellin дефект.** Искать norm-controlled карту от centered residual \(R_N\) к полному finite-window functional, с paid endpoint и exact Gamma. Kill-power высокий: правильный off-line evaluation witness; цена высокая, потому что несглаженный carrier имеет лишь алгебраические частотные хвосты. Нужно улучшить именно хвост C20, а не переоптимизировать уже исчерпанный T.

B. **Одно Gaussian-окно и арифметический squared residual.** Работать с явным (7.9)–(7.12), сохраняя head/tail вместе, либо с оптимальными Schur gains исходного residue-Gram. Kill-power высокий: ненулевой Laplace residue; аналитическая цена определения низкая, цена cofinal inverse-log bound остаётся неизвестной. Нельзя считать выбор хорошего finite interpolant доказательством его хвоста.

Ни A, ни B не являются новым обязательным барьером для любого доказательства RH. Generic Poisson return RB, backward damping, null-gauge и свободный путь не используются как поставщики знака.

## 12. Closeout и проверка доставки

Закрыты точное центрирование, избыточный показатель 6 в full-window пороге, конечный NB→Gaussian горизонт и фактор 2 в разнесении.
Не закрыты безусловный rate, globally optimal full-window coupling и RH.
Ни один истинный нуль не исключён новой безусловной оценкой: `RH_SIGN_PROGRESS: NONE`.

```yaml
iteration:
  target: NATURAL_CENTERED_NB_TO_WINDOW_COUPLING
  status: PROGRESS
  cognitive_operator_used: SCALE_AUDIT_AND_RECEIVER_MATCHING
  new_gap_name: INVERSE_LOG_CENTERED_RESIDUE_RATE_OR_FULL_PHYSICAL_MELLIN_TRANSFER
  invariant_learned: FINITE_ONE_VECTOR_BRIDGE_IS_NOT_ONE_CELL_FULL_MATRIX_PSD
  forbidden_future_move: IDENTIFY_OPTIMAL_NB_DISTANCE_WITH_VN_ERROR_OR_DROP_EXACT_GAMMA
  next_decisive_test: SOURCE_BOUND_FOR_FULL_CENTERED_FEJER_RESIDUAL_OR_PHYSICAL_TAIL
  route_score: 3
```

Созданы только отдельный freeze и данный новый verdict с суффиксом `_B`.
Freeze commit `97f4cf0380adf863bb8cd4c663fc05b2a30488b3`, blob `27dd83d293ef2150a34cd01040e80f4d7c6fbe34`.
Ветка обоих файлов: `proshka_inbox_2026-10-31`.
Пути:
```text
docs/routeB_bus/proshka/PROSHKA_FREEZE_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md
docs/routeB_bus/proshka/PROSHKA_VERDICT_ROUND7_NB_WINDOW_COUPLING_2026-11-06_B.md
```
Freeze не редактировался. Старые вердикты, route-state и Lean не изменены.
Финальный commit и blob сообщаются в квитанции после remote create/readback; самореферентный commit hash в собственные bytes не встраивается.
Проверка хеша — проверка доставки, не математический аудит.

**RH_PROVED: false.**
