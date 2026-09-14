# STATUS: KILL_NAMED_PHI_SPIN_CONSTRUCTION
```yaml
OPERATIVE_CLASS: KILL_NAMED_PHI_SPIN_CONSTRUCTION
REQUEST_ID: REQ-2026-09-12-LYGSPHI
BOUNDARY_ID: GOAL058_ACTUAL_THETA_FERROMAGNETIC_REALIZATION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
SOURCE_BASE: 7653a3503d20be4dba91a333ff96e5eea30c738c
ACCEPTED_DELTA_COMMIT: f40db276e8f3c4c4d47adec755e5fb72691a4999
REQUEST_COMMIT_FROM_BINDER: d6cbfa02d9604f2aeba2e70b6daaebff80c0859a
REQUEST_REMOTE_REFETCHED: false
REQUEST_SHA256_VERIFIED: 32d75bc0235c8aaa48c326e240b5e1123d914d0caf8ea568a86402adb0ae2e71
REQUEST_GIT_BLOB_VERIFIED: 1d8d84e660e4cb503ce44dfe86ba0f661160e33b
REQUEST_BYTES: 89217
REQUEST_LF: 1384
REQUEST_FINAL_LF: true
REQUEST_CR: 0
COMPLETE_CONTROLLING_REQUEST_READ: true
COMPLETE_EMBEDDED_REPORTS_READ: 4
EMBEDDED_REPORT_HASHES_MATCH: 4
RECURSIVE_ARCHIVE_REREAD: false
CONSTRUCTION: SOURCE_ENTROPY_CORRECTED_CRITICAL_BINOMIAL_BLOCK
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: EXACT_SOURCE_CONDITIONAL_ODDS_UPPER_ENVELOPE
KILL_EVIDENCE: "This artifact, Theorem C, equations (16)-(23)"
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
EPISTEMIC_SCOPE: THIS_EXACT_JOINT_LIFT_ONLY
RESULT_SCOPE: SOURCE_DERIVED_FINITE_SPIN_CONSTRUCTION_TEST_NOT_GENERAL_GS_EXCLUSION
EVIDENCE_STATUS: PAPER_CANDIDATE_PENDING_INDEPENDENT_REVIEW
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
BASE_PAIR_COUPLINGS_NONNEGATIVE: PROVED
OBSERVABLE_WEIGHTS_POSITIVE: PROVED
CORRECTED_SOURCE_LAWS_WEAKLY_CONVERGE: PROVED
CORRECTED_SOURCE_LAWS_UNIFORM_EXPONENTIAL_MOMENTS: PROVED
CORRECTED_SOURCE_TRANSFORMS_LOCALLY_UNIFORM: PROVED
CORRECTED_LAWS_FERROMAGNETIC_PAIR: REFUTED
SAME_VISIBLE_LAW_HIDDEN_FERROMAGNETIC_REPAIR: REFUTED
GENERAL_PHI_GRIFFITHS_SIMON_REALIZATION: OPEN
NEGATIVE_ACTUAL_HANKEL_OR_K_WITNESS: NOT_PRODUCED
GLOBAL_ODD2: OPEN
GLOBAL_IC: OPEN
ALL_ORDER_SOURCE_SIGN: OPEN
NEW_SOURCE_SIGN: false
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: BOUNDARY_CASE
ROUTE_SCORE_FOR_TESTED_CONSTRUCTION: 4
SOURCE_SIGN_NO_DELTA_COUNT:
  initial: 2
  proposed_after_independent_intake: 3
  machine_counter_changed: false
SOURCE_NUMERICAL_EVALUATIONS: 0
HANKEL_NUMERICAL_TESTS: 0
LEAN_RUNS: 0
REPOSITORY_WRITES: 0
PRODUCTION_ADMISSION: false
PX_RH_CLAIM: NOT_MADE
```

## 1. Физический объект и результат опыта

Ы. Строю **один равновесный блок бинарных спинов**. Все спины входят в намагниченность с одинаковым положительным весом. Начальный блок имеет явные неотрицательные парные связи. Затем проверяю одну конкретную операцию: точное перевзвешивание уровней намагниченности полной исходной **theta-плотностью**, с компенсацией числа микросостояний каждого уровня.

Смысл операции простой. Одно значение намагниченности возникает у многих спиновых конфигураций. Чтобы получить именно заданную плотность, нужно учитывать эту **биномиальную кратность**, а не писать только энергию `−log p`.

Опыт дал разделённый результат. Исправленные распределения намагниченности действительно сходятся к **той же** \(p=\Phi/Z\), и вся требуемая равномерная экспоненциальная интегрируемость доказана. Но исправленный блок **не является парным ферромагнетиком**: условная связь двух спинов при почти полном выравнивании строго отрицательна. Её точная верхняя огибающая меньше \(-2\).

Поэтому свойство **Lee–Yang** — отсутствие нулей функции распределения по комплексному полю вне мнимой оси — переносить с исходного ферромагнитного блока на исправленную модель нельзя. Успешная сходимость относится к исправленной модели; ферромагнитность — к другой, исходной. Смешивать эти два семейства нельзя.

Это **строгий отказ данной конструкции**, не доказательство того, что \(\Phi/Z\) не имеет никакой реализации Griffiths–Simon. В частности, не получен отрицательный свидетель для исходных \(H_n\), \(K_-\) или \(Q\).

Все новые результаты ниже — **PAPER-кандидаты**, то есть математические доказательства для последующего независимого приёма, не проверка ядром Lean.

## 2. Источники и точная область чтения

### 2.1. Авторитетный пакет

Полностью прочитаны управляющая часть и четыре декодированных отчёта. Сняты ровно два транспортных ASCII-символа `| ` в начале каждой строки; число строк задаётся рамкой. Все размеры, LF, SHA-256 и конечные LF совпали. Манифест находится в приложении A.

Обозначения внутренних источников:

* **S1** — `REPORT_2026-09-12_PHYSICS_BROTHER_LEE_YANG.md`: физический интерфейс, точная \(L^1\)-нормировка и принятые ограничения.
* **S2** — `REPORT_2026-09-12_ALL_ODD_TO_RH.md`: полная исходная Fourier/xi-идентификация и условная all-order редукция.
* **S3** — `SLACK_INDEPENDENT_CHECK_2026-09-11.md`: исходные \(r,\Phi\), полная theta-серия, BP1 и границы уже проверенных контролей.
* **S4** — `REPORT_2026-09-12_SOURCE_MOMENT_HANKEL_INTERFACE.md`: гладкость, исходная кривизна и интегрируемость моментов. Его Hankel/Stein-разложение не продолжается в данном опыте.

Исторические pending-строки внутри S3 читаются вместе с его последующими acceptance receipts. Принимаются ровно указанные там области. Отсутствующие рекурсивные зависимости не объявляются заново прочитанными. Коммит доставки указан по binder; запрос повторно из remote не скачивался. Для байтов самого запроса авторитетно вложение, и его Git blob пересчитан непосредственно.

### 2.2. Первичные физические источники

**P1.** Simon–Griffiths, *The (phi^4)_2 field theory as a classical Ising model*, CMP 33 (1973), 145–164. Непосредственно проверены определения §2, Theorem 1 и Theorem 3; просмотрены страницы 147–152, в том числе изображения определений и формул на 147, 148, 150–152. Используются устройство биномиального блока и ограничения парного ферромагнетика, не готовая принадлежность \(p\) классу Lee–Yang.

**P2.** Aizenman–Fernandez, *On the critical behavior of the magnetization in high-dimensional Ising models*, JSP 44 (1986). Непосредственно прочитаны и визуально проверены Appendix C, страницы 449–450, (C.2)–(C.6): положительные веса микроспинов и ферромагнитные внутриблоковые связи.

Адреса прочитанных страниц:

```text
P1: https://math.caltech.edu/SimonPapers/47.pdf
P2: https://webspace.science.uu.nl/~ferna107/papers/_86_Aiz_Fern_highd.pdf
```

Просмотр выполнен через web PDF и screenshot. Хеши PDF-копий из S1 остаются **унаследованными квитанциями**: текущие PDF-байты в контейнер не получены, поэтому эти хеши здесь заново не сертифицируются. Это не ограничивает приведённое ниже элементарное доказательство отказа; оно выписано полностью.

Буквальная Lemma 4 P1 не импортируется. Коэффициент на странице 150 читается как \(N^{-1}/2=1/(2N)\). Готовый quartic tail mismatch и старый BFS-контроль не пересчитываются и не выдаются за результат этого опыта.

## 3. Регистрация до проверки

Выбрана **одна** конструкция `SOURCE_ENTROPY_CORRECTED_CRITICAL_BINOMIAL_BLOCK`. До проверки в сообщении зарегистрированы два ожидания:

**P_LIMIT:** точное исходное перевзвешивание даст слабую сходимость к \(\Phi/Z\) и требуемые равномерные экспоненциальные моменты.

**P_EDGE:** то же перевзвешивание может сделать условную пару у края антиферромагнитной.

Проверочный **дискриминатор** — отношение четырёх условных вероятностей. У парного ферромагнетика оно обязано быть не меньше единицы. Его знак предварительно проверен на нейтральной, ферромагнитной и намеренно антиферромагнитной трёхспиновых моделях; результаты и точный код в приложении B. Никакой прогноз о ложности RH или отсутствии всех GS-реализаций не регистрировался.

## 4. Полная исходная функция и начальный ферромагнетик

### 4.1. Нормировка

Сохраняются буквально

\[
r(t)=2\sum_{n\ge1}(2\pi^2n^4t-3\pi n^2)e^{-\pi n^2t},\qquad
\Phi(x)=e^{5x/2}r(e^{2x}),
\]
\[
Z=\int_{\mathbb R}\Phi(x)\,dx=\xi(1/2)>0,\qquad
p(x)=\Phi(x)/Z.
\tag{1}
\]

Здесь \(Z\) — **\(L^1\)-нормировка**. Физическая \(A=\|\Phi\|_2\) не заменяется, но в данной вероятностной конструкции не нужна. В старой записи BP1 S3 буква \(I\) обозначает нынешний \(Z\), а \(\mathbb E[T^{1/4}]=2Z\); этот множитель не теряется.

Из S1–S4 используются: \(\Phi>0\), чётность, гладкость, строгий максимум в нуле, \(\ell''(0)<0\) для \(\ell=\log\Phi\), а также

\[
\int_{\mathbb R}e^{R|x|}\bigl(\Phi(x)+|\Phi'(x)|\bigr)\,dx<\infty
\quad\text{для каждого }R\ge0.
\tag{2}
\]

Это полные исходные свойства, не свойства конечной обрезки.

### 4.2. Явные веса и положительные парные связи

Определим исходное число

\[
\gamma_\Phi=-\ell''(0)>0,
\qquad
k_0=\max\{4,\lceil\sqrt{\gamma_\Phi+1}\rceil\}.
\]

\(\gamma_\Phi\) определено полной theta-серией и её производными, не нулями xi. Численная оценка \(\gamma_\Phi\) для доказательства не нужна: выбор \(k_0\) сам гарантирует последующий знак.

Для каждого целого \(k\ge k_0\) положим

\[
n_k=k^4,\qquad \delta_k=k^{-3},\qquad
q_{i,k}=\delta_k>0,
\]
\[
S(\sigma)=\sum_{i=1}^{n_k}\sigma_i,\qquad
X_k=\delta_kS(\sigma),\qquad |X_k|\le k.
\tag{3}
\]

Начальный **полносвязный блок** имеет связи

\[
J^0_{ij,k}=J^0_k=k^{-4}-\gamma_\Phi k^{-6}
=\frac{k^2-\gamma_\Phi}{k^6}\ge k^{-6}>0,
\qquad i<j.
\tag{4}
\]

Его закон:

\[
\mathbb P^0_k(\sigma)
=\frac1{\mathcal Z^0_k}
\exp\!\left(J^0_k\sum_{i<j}\sigma_i\sigma_j\right).
\]

Это настоящий конечный парный ферромагнетик при нулевом внешнем поле. Равенство \(\sum_{i<j}\sigma_i\sigma_j=(S^2-n_k)/2\) делает его распределение намагниченности явным. Коэффициент в (4) совмещает критический биномиальный масштаб P1 с квадратичным коэффициентом самого источника. Положительность (4) доказана до любых предельных операций.

Совпадение одного коэффициента не идентифицирует предел. Поэтому далее выполняется не такой вывод, а точная проверяемая исходная коррекция.

## 5. Одна операция, вставляющая весь источник

Для \(s\in\{-n_k,-n_k+2,\ldots,n_k\}\) биномиальная кратность равна

\[
B_k(s)=\binom{n_k}{(n_k+s)/2}.
\]

Умножим исходный закон на **точный множитель перевзвешивания**

\[
\mathcal R_k(s)=
\frac{\Phi(\delta_ks)}{B_k(s)}
\exp\!\left(-\frac{J^0_k}{2}s^2\right)>0
\tag{5}
\]

и нормируем. В результате получается буквально

\[
\boxed{
\mathbb P^\theta_k(\sigma)=
\frac{\Phi(\delta_kS(\sigma))}
{C_k B_k(S(\sigma))},
\qquad
C_k=\sum_{s=-n_k,-n_k+2,\ldots,n_k}\Phi(\delta_ks).
}
\tag{6}
\]

Причина: \(e^{J^0_k(S^2-n_k)/2}\mathcal R_k(S)\) отличается от \(\Phi(\delta_kS)/B_k(S)\) только постоянным множителем. Суммирование по каждой орбите из \(B_k(s)\) конфигураций доказывает нормировку (6).

В частности,

\[
\boxed{
\mathbb P^\theta_k(X_k=\delta_ks)=\frac{\Phi(\delta_ks)}{C_k}.
}
\tag{7}
\]

Получена конечная положительная спиновая мера с точной \(\Phi\)-формулой, нулевым вставленным полем и инвариантностью относительно переворота всех спинов. Её формальный гамильтониан равен

\[
\mathcal H^\theta_k(\sigma)
=-\log\Phi(\delta_kS(\sigma))+\log B_k(S(\sigma))
\tag{8}
\]

с точностью до константы. **Ни (8), ни его чётность не объявляются доказательством парности или ферромагнитности.** Эти свойства проверяются ниже. Именно операция (5), а не формальное название (8), является предметом опыта.

Это **не** повтор переноса независимости Gamma-компонент на логарифм. Конструкция начинается непосредственно с полной \(\Phi\), учитывает кратности конечного спинового носителя и не приписывает \(X\) независимые слагаемые.

## 6. Теорема A: весь вероятностный и комплексный предел оплачен

**Утверждение.** Для исправленных законов (6)

\[
X_k\Rightarrow p(x)\,dx,
\qquad
\sup_{k\ge k_0}\mathbb E^\theta_k e^{R|X_k|}<\infty
\quad(R>0),
\]
\[
M^\theta_k(h)=\mathbb E^\theta_ke^{hX_k}
\longrightarrow
M(h)=\frac1Z\int e^{hx}\Phi(x)\,dx
\quad\text{локально равномерно на }\mathbb C.
\tag{9}
\]

Все три утверждения относятся к **одной исправленной семье** (6).

### 6.1. Полная ошибка интегральной суммы

Введём шаг \(a_k=2\delta_k=2k^{-3}\). Узлы равны

\[
x_{j,k}=-k+a_kj,\qquad 0\le j\le n_k.
\]

Их клетки \([x_{j,k}-\delta_k,x_{j,k}+\delta_k)\) без разрывов покрывают \([-k-\delta_k,k+\delta_k)\). Это верно и для нечётного \(k\), когда ноль не обязан быть узлом.

Для абсолютно непрерывной функции \(g\), \(g'\in L^1\), на каждой клетке

\[
\int_{I_{j,k}}|g(x_{j,k})-g(t)|\,dt
\le a_k\int_{I_{j,k}}|g'(t)|\,dt.
\]

Поэтому

\[
\left|a_k\sum_jg(x_{j,k})-\int_{\mathbb R}g(t)\,dt\right|
\le a_k\|g'\|_1+\int_{|t|>k}|g(t)|\,dt.
\tag{10}
\]

Обе бесконечные стороны интеграла сохранены.

Положим

\[
W_R=\int e^{R|t|}\Phi(t)\,dt,
\qquad
A_R=\int e^{R|t|}\bigl(|\Phi'(t)|+R\Phi(t)\bigr)\,dt.
\]

Из (2) они конечны. Для \(|h|\le R\), \(g_h(t)=e^{ht}\Phi(t)\), правая часть (10) не превосходит

\[
\varepsilon_R(k)=2k^{-3}A_R+e^{-k}W_{R+1}.
\tag{11}
\]

Здесь оценка хвоста — точное неравенство
\(e^{R|t|}\mathbf1_{|t|>k}\le e^{-k}e^{(R+1)|t|}\), а не асимптотика без константы.

Обозначим

\[
D_k=a_kC_k,\qquad
N_k(h)=a_k\sum_je^{hx_{j,k}}\Phi(x_{j,k}).
\]

Тогда \(|D_k-Z|\le\varepsilon_0(k)\) и
\(\sup_{|h|\le R}|N_k(h)-\int e^{ht}\Phi(t)dt|\le\varepsilon_R(k)\).

Выберем целое \(k_1\ge k_0\), для которого \(\varepsilon_0(k_1)\le Z/2\). Оно существует; обе части (11) убывают с \(k\). Для всех \(k\ge k_1\), \(D_k\ge Z/2\), и

\[
\boxed{
\sup_{|h|\le R}|M^\theta_k(h)-M(h)|
\le\frac2Z\left(\varepsilon_R(k)+\frac{W_R}{Z}\varepsilon_0(k)\right)
\longrightarrow0.
}
\tag{12}
\]

Это прямой бюджет для полного комплексного преобразования конкретной конструкции, не повтор абстрактной условной стрелки.

### 6.2. Равномерные экспоненциальные моменты последовательности

Для \(g(t)=e^{R|t|}\Phi(t)\) применима (10); функция абсолютно непрерывна, а её производная почти всюду оценивается выражением в \(A_R\). Используя только клетки, получаем

\[
a_k\sum_je^{R|x_{j,k}|}\Phi(x_{j,k})
\le W_R+a_kA_R.
\]

Поэтому

\[
\boxed{
\sup_{k\ge k_0}\mathbb E^\theta_ke^{R|X_k|}
\le
\max\left\{e^{Rk_1},\frac2Z\bigl(W_R+2k_0^{-3}A_R\bigr)\right\}<\infty.
}
\tag{13}
\]

Первый член оплачивает все конечные начальные \(k<k_1\), поскольку \(|X_k|\le k\). Это **равномерность по всей последовательности**, не только момент предельного \(p\).

Для слабой сходимости достаточно на фиксированном компакте применить обычную сходимость интегральных сумм к непрерывной ограниченной тестовой функции. Хвосты всей семьи равномерно исчезают по (13) с \(R=1\). Нормировки сходятся по (10). Получается первое утверждение (9). Теорема A доказана.

**Граница:** теорема A ничего не утверждает о положении нулей \(M^\theta_k\). Для него ещё нужна ферромагнитность именно \(\mathbb P^\theta_k\), а не \(\mathbb P^0_k\).

## 7. Теорема B: необходимый локальный тест парной ферромагнитности

Для любой строго положительной меры \(P\) на \(\{-1,1\}^n\), двух индексов \(i,j\) и фиксированных остальных спинов \(\tau\) определим

\[
\mathcal O_{ij}(\tau)=
\frac{P(\sigma_i=+,\sigma_j=+,\tau)P(\sigma_i=-,\sigma_j=-,\tau)}
{P(\sigma_i=+,\sigma_j=-,\tau)P(\sigma_i=-,\sigma_j=+,\tau)}.
\tag{14}
\]

Это **условное отношение шансов**: общая нормировка и вероятность условия сокращаются. Для закона

\[
P(\sigma)\propto
\exp\left(\sum_{a<b}J_{ab}\sigma_a\sigma_b+\sum_a h_a\sigma_a\right)
\]

прямое раскрытие четырёх энергий даёт

\[
\boxed{\mathcal O_{ij}(\tau)=e^{4J_{ij}}.}
\tag{15}
\]

Связи с фиксированными спинами и все поля сокращаются точно. В частности, при \(J_{ij}\ge0\) отношение не меньше единицы и не зависит от \(\tau\).

Для произвольной меры \(\frac14\log\mathcal O_{ij}(\tau)\) — единственный коэффициент взаимодействия в её **двухспиновом условном законе**. Его нельзя автоматически считать одной глобальной парной константой: при многоспиновых взаимодействиях он зависит от окружения.

Тест (15) проверен точными рациональными planted-моделями: отсутствие связей даёт 1; \(J_{12}=\log2\) даёт 16; намеренный отрицательный \(J_{12}=-\log2\) даёт \(1/16\), независимо от третьего спина. Это проверка инструмента, не вычисление theta.

## 8. Теорема C: исходная коррекция создаёт строго отрицательную связь

**Утверждение.** Исправленный закон (6), определённый и для всех целых \(k\ge4\), удовлетворяет

\[
\boxed{
\mathcal O_{12}(+,+,\ldots,+)<\frac1{10000},
\qquad
J^{\mathrm{eff}}_{12}(+,+,\ldots,+)
=\frac14\log\mathcal O_{12}<-\log10<-2.
}
\tag{16}
\]

Следовательно, ни при одном таком \(k\) он не представим парным ферромагнетиком на этих спинах. В частности, это верно на всей последовательности \(k\ge k_0\).

### 8.1. Точные четыре исходных веса

Зафиксируем все спины, кроме первых двух, равными \(+1\). Намагниченности четырёх конфигураций:

\[
k,\quad k-2\delta_k,\quad k-2\delta_k,\quad k-4\delta_k.
\]

Их ненормированные веса по (6) равны

\[
\Phi(k),\qquad
\frac{\Phi(k-2\delta_k)}{n_k},\qquad
\frac{\Phi(k-2\delta_k)}{n_k},\qquad
\frac{2\Phi(k-4\delta_k)}{n_k(n_k-1)}.
\]

Поэтому

\[
\boxed{
\mathcal O_k=
\frac{2n_k}{n_k-1}
\frac{\Phi(k)\Phi(k-4\delta_k)}{\Phi(k-2\delta_k)^2}.
}
\tag{17}
\]

Это точный четырёхконфигурационный объект, построенный из **нашей** \(\Phi\). На самом маленьком контрольном индексе \(k=4\) имеем 256 спинов и аргументы \(4,127/32,63/16\). Численные значения \(\Phi\) даже здесь не вычисляются.

### 8.2. Полный theta-бюджет

Из (1) при \(a=\pi e^{2x}\) точно следует

\[
\Phi(x)=4\pi^2 e^{9x/2-a}H(a),
\]
\[
H(a)=1-\frac3{2a}+E(a),\qquad
E(a)=\sum_{n\ge2}\left(n^4-\frac{3n^2}{2a}\right)e^{-(n^2-1)a}.
\tag{18}
\]

Для \(a\ge100\) все слагаемые \(E\) положительны. Если
\(t_n=n^4e^{-(n^2-1)a}\), то

\[
\frac{t_{n+1}}{t_n}
\le\frac{81}{16}e^{-5a}<\frac12
\qquad(n\ge2).
\]

Следовательно,

\[
0<E(a)\le32e^{-3a}\le32e^{-300}<\frac1{100}.
\]

Получен полный, а не одно-модовый, интервал

\[
\boxed{\frac9{10}<H(a)<\frac{11}{10}\qquad(a\ge100).}
\tag{19}
\]

Для \(k\ge4\) самый малый аргумент \(x_-=k-4/k^3\) больше 3. Поэтому \(\pi e^{2x_-}>3\cdot2^6=192>100\), и (19) применим ко всем трём исходным точкам.

Линейные множители \(e^{9x/2}\) из (18) в отношении (17) сокращаются. Экспоненциальный дефект равен точно

\[
D_k=\pi\bigl(e^{2k}+e^{2(k-4\delta_k)}-2e^{2(k-2\delta_k)}\bigr)
=\pi e^{2(k-4\delta_k)}(e^{4\delta_k}-1)^2.
\tag{20}
\]

Из \(e^z-1\ge z\), \(\pi>3\) и \(8/k^3<1\):

\[
D_k>\frac{48e^{2k-1}}{k^6}.
\]

Функция \(e^{2k-1}/k^6\) возрастает для вещественных \(k\ge4\), поскольку её логарифмическая производная \(2-6/k>0\). Используя \(e>8/3\), получаем универсальный рациональный запас

\[
\boxed{D_k>\frac{48(8/3)^7}{4^6}=\frac{8192}{729}>11.}
\tag{21}
\]

Полный множитель перед \(e^{-D_k}\) оценивается как

\[
\frac{2k^4}{k^4-1}\left(\frac{11}{9}\right)^2
\le\frac{512}{255}\frac{121}{81}
=\frac{61952}{20655}<4.
\]

Итак,

\[
\boxed{
\mathcal O_k<4e^{-11}
<4(3/8)^{11}
=\frac{177147}{2147483648}
<\frac1{10000}.
}
\tag{22}
\]

Это **строгая верхняя огибающая** исходного отношения. Все моды, все коэффициенты биномиальной кратности и нормировки включены. Ни одна равномерность по \(k\) не заменена конечным тестом.

Из (22), \(e<3\) и \(e^2<9<10\) следует вторая часть (16). Теорема C доказана.

### 8.3. Точное место потери

У начального блока (4) отношение равно \(e^{4J^0_k}>1\). У множителя (5) его четырёхточечное отношение равно

\[
\mathcal O(\mathcal R_k)=\mathcal O_k e^{-4J^0_k}<\frac1{10000}.
\tag{23}
\]

Значит операция, которая вставляет **весь** источник, не реализуется добавлением неотрицательных парных связей к начальному блоку. Положительность самого множителя \(\mathcal R_k\) этого не исправляет.

Это не известное сравнение quartic-хвоста с theta-хвостом. Здесь построен конкретный конечный источник-зависимый закон, оплачен весь его предел и предъявлен **неасимптотический антиферромагнитный условный коэффициент** на каждом индексе семейства.

## 9. Скрытые ферромагнитные спины не исправляют тот же совместный закон

Можно попытаться представить (6) как маргинальный закон видимых спинов после суммирования по дополнительным ферромагнитным спинам. Для этой точной попытки тоже имеется запрет.

**Локальная лог-сверхмодулярность** означает: на каждой бинарной грани произведение двух согласованных весов не меньше произведения двух противоположных весов, то есть (14) не меньше единицы. Положительные парные взаимодействия дают это свойство по (15).

Докажем его сохранение при исключении одного бинарного спина без внешней теоремы. Зафиксируем остальные спины и запишем восемь положительных весов, после деления на \(f_{000}\), в виде

\[
\begin{array}{c|cccccccc}
(i,j,z)&000&100&010&001&110&101&011&111\\ \hline
f_{ijz}&1&x&y&z&xy\alpha&xz\beta&yz\gamma&xyz\delta.
\end{array}
\]

Неотрицательность четырёх соответствующих граней даёт
\(\alpha,\beta,\gamma\ge1\) и \(\delta\ge\beta\gamma\). Для маргинальных весов \(g_{ij}=f_{ij0}+f_{ij1}\):

\[
\begin{aligned}
g_{00}g_{11}-g_{10}g_{01}
=xy\bigl[(\alpha-1)
+z(\alpha+\delta-\beta-\gamma)
+z^2(\delta-\beta\gamma)\bigr]\ge0,
\end{aligned}
\tag{24}
\]

поскольку
\(\alpha+\delta-\beta-\gamma\ge1+\beta\gamma-\beta-\gamma
=(\beta-1)(\gamma-1)\ge0\).

После каждой элиминации аргумент применяется к любой паре оставшихся координат и любому фиксированному окружению. Индукция исключает произвольное конечное число скрытых спинов. Замкнутость неравенства исключает также пределы таких маргинальных законов на фиксированном конечном видимом носителе.

По (22) совместный закон (6) этого свойства не имеет. Следовательно:

\[
\boxed{
\begin{gathered}
\mathbb P^\theta_k\text{ не является видимым маргинальным законом}\\
\text{конечной парной ферромагнитной системы.}
\end{gathered}
}
\tag{25}
\]

Результат допускает даже произвольные вещественные внешние поля у скрытой системы: они сокращаются из (15). Поэтому введение их не спасает указанную точную маргинализацию.

**Область (25) фиксирована.** Если новые спины также входят в измеряемую намагниченность, это уже другой наблюдаемый объект. Если меняется совместный закон видимых спинов, сохраняя только его суммарную намагниченность, (25) также не является запретом. Эти варианты не проверены данным доказательством.

Есть количественная устойчивость: ферромагнитный маргинал не может иметь отношения к четырём вероятностям нашего свидетеля одновременно в диапазоне \([1/10,10]\). Иначе его odds были бы меньше \(10^4\mathcal O_k<1\). Это большой **относительный** дефект на данных конфигурациях; не утверждение о большой абсолютной вероятностной ошибке.

## 10. Сильнейшая атака на вывод и точная граница отказа

**Возражение:** антиферромагнитный свидетель находится около намагниченности \(k\to\infty\). Вероятность таких конфигураций исчезает. Почему это должно исключать другую аппроксимацию того же \(p\)?

**Ответ:** не должно. По (13), если \(B=\sup_k\mathbb E^\theta_ke^{|X_k|}<\infty\), то

\[
\mathbb P^\theta_k\{|X_k|\ge k/2\}\le Be^{-k/2}\longrightarrow0.
\tag{26}
\]

Для \(k\ge4\) все четыре конфигурации (17) находятся внутри этого хвостового события. Поэтому строгий отказ точного совместного закона не создаёт нижней положительной границы расстояния между \(p\) и всеми пределами ферромагнитных намагниченностей.

В частности, доказательство **не** устанавливает:

\[
p\notin GS,
\qquad
M(h_0)=0\text{ при }\Re h_0\ne0,
\qquad
H_n\not\succeq0,
\qquad
K_-\not\succeq0.
\]

Не установлено и существование хорошего ферромагнитного ремонта. Малость вероятности испорченных микросостояний лишь объясняет, почему отказы (16), (25) нельзя повышать до отказа общей предельной программы.

Нельзя удалить эти конфигурации и затем назвать результат парным ферромагнетиком: жёсткое обрезание или произвольная модификация энергии требует новой проверки всех связей и всех предельных оценок.

## 11. Точная оставшаяся обязанность и два ограниченных ремонта представления

Для исходного конечного потребителя нужны **одна и та же** семья неотрицательных \(J_{ij,N}\), положительных \(q_{i,N}\), её закон намагниченности и требуемые пределы. В этом опыте имеются две несовместимые строки:

\[
\mathbb P_k^0:\quad J^0_{ij,k}>0\quad\text{доказано};
\]
\[
\mathbb P_k^\theta:\quad X_k\Rightarrow p,\quad
\sup_k\mathbb E e^{R|X_k|}<\infty\quad\text{доказано},
\quad\text{ферромагнитность опровергнута}.
\]

**FIRST_FAILURE:** переход (5) от \(\mathbb P^0_k\) к \(\mathbb P^\theta_k\) теряет неотрицательные парные связи; точный свидетель — (17)–(23).

**MINIMAL_MISSING_INTERFACE:** допустимая ферромагнитная семья, для которой все изменения исходной меры оплачены в том же предельном наблюдаемом. Ни S1, ни P1/P2 не предоставляют такой семьи для \(\Phi\).

Чтобы обозначить пределы этой остановки, фиксируются два возможных изменения представления. Они **не выполнялись и не являются новыми положительными поставщиками**:

| Представление | Точный контракт к тому же потребителю | Сила проверки / стоимость, экспертная оценка |
|---|---|---|
| **Только гистограмма намагниченности, без равенства совместных законов** | Найти \(J_{ij,k}\ge0\), для которых индуцированные массы \(w_{J,k}(s)\) удовлетворяют \(\sum_s e^{R\delta_k|s|}|w_{J,k}(s)-\Phi(\delta_ks)/C_k|\to0\) для каждого \(R>0\). В сочетании с (12),(13) это оплачивает весь предел, не требуя (25). | Решительность 9/10; стоимость 9/10. Неравенства для симметризованного совместного закона не подменяют этот контракт. |
| **Положительная кластерная сумма вместо конфигурационного логарифма** | Для \(v_e=e^{2J_e}-1\ge0\) точно развернуть вес по рёбрам: нормированное преобразование равно взвешенному среднему \(\prod_C\cosh(h\sum_{i\in C}q_i)\) с весами \(2^{\#C}\prod_{e\in A}v_e\). Требуется исходный выбор рёбер/весов и сходимость именно этого среднего к \(M\). | Решительность 9/10; стоимость 8/10. Само среднее положительных кластерных весов не доказывает его тождество theta. |

Вторая запись получается прямо из
\(e^{J_e\sigma_i\sigma_j}=e^{-J_e}[1+(e^{2J_e}-1)\mathbf1_{\sigma_i=\sigma_j}]\): после раскрытия произведения спины постоянны на компонентах выбранных рёбер, а суммирование по их знакам даёт cosh. Это лишь точное альтернативное представление. Новый источник связей в нём не найден; отдельный конструктивный опыт не запускается.

Оценки стоимости — не вероятности доказательства RH. Ни одно из этих переобозначений не сбрасывает счётчик.

## 12. Ledger, зависимости и границы утверждений

| Утверждение | Scope | Verifier | Статус и зависимость |
|---|---|---|---|
| \(p=\Phi/Z\), \(M(h)=\xi(1/2+h)/\xi(1/2)\) | ABSTRACT | PAPER | Принятый S1/S2, не заново доказанный полный transfer audit |
| Положительные \(q_{i,k},J^0_{ij,k}\) начального блока | COFINAL_FAMILY | PAPER | Новая формула (3),(4), исходная конечная \(\gamma_\Phi\) из S4 |
| Исправленный закон и точные массы намагниченности | COFINAL_FAMILY | PAPER | Новые (5)–(8), полный источник S3 |
| Слабая сходимость, равномерные моменты и локально равномерные transforms исправленного закона | COFINAL_FAMILY | PAPER | Теорема A, (2),(10)–(13) |
| Ферромагнитный conditional odds-тест | ABSTRACT | PAPER | Элементарное точное раскрытие (15) |
| Полный theta-контроль \(H\) в трёх точках для всех \(k\ge4\) | COFINAL_FAMILY | PAPER | (18)–(22), геометрическая мажоранта всего ряда |
| \(J^{eff}<-2\) для исходно исправленного блока | COFINAL_FAMILY | PAPER | Теорема C; это upper-envelope kill указанной конструкции |
| Скрытая ферромагнитная маргинализация не сохраняет тот же видимый закон | ABSTRACT | PAPER | (24),(25), доказательство исключения бинарных переменных |
| Девять рациональных сравнений и plants | FINITE_CELL | PAPER | Исполненный Appendix B; не ARB_INTERVAL и не LEAN |
| Два альтернативных интерфейса | COFINAL_FAMILY | CONDITIONAL | Определены, но источник связей/ошибки не получен |
| Общая GS-реализация \(\Phi/Z\) и полный source sign | COFINAL_FAMILY | CONDITIONAL | Открыты; данная конструкция их не опровергает |

Для любого нового PAPER-результата этой таблицы независимый приём ещё требуется. Обозначение «доказано» относится к выведенному здесь математическому утверждению, не к каноническому статусу проекта.

### K8A — consumer-first граница

```yaml
DOWNSTREAM_CONSUMER: finite_Lee_Yang_plus_same_family_local_uniform_limit_for_actual_M
ACTUAL_CONSUMER_REQUIREMENT: >-
  One source-derived zero-field pair ferromagnetic family with positive
  observable weights and convergence to the actual Phi/Z law, with all
  uniform exponential moments or an equivalent proved transform limit.
ORIGINAL_REQUESTED_OBJECT: a ferromagnetic realization of the actual Phi/Z
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_NOTE: >-
  The interface is sufficient; necessity for every possible RH proof is not asserted.
TESTED_OBJECT: exact exchangeable entropy-corrected critical binomial joint law
TESTED_OBJECT_IS_NECESSARY: false
KNOWN_WEAKER_INTERFACES:
  - only the magnetization histogram must converge; joint-law equality is unnecessary
  - direct locally uniform convergence of admissible ferromagnetic transforms suffices
FAILURE_TYPE: INCOMPATIBILITY
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: exact full-source negative conditional pair coupling
PINNED_EVIDENCE: equations (17)-(23) and literal arithmetic output in Appendix B
EPISTEMIC_STATUS_OF_TESTED_EXACT_LIFT: MATHEMATICALLY_DEAD
EPISTEMIC_STATUS_OF_GENERAL_REALIZATION: RESEARCH_DEBT
REOPEN_TRIGGER: >-
  A different microscopic lift or an admissible asymptotic correction whose
  nonnegative pair couplings and source-observable convergence are independently proved.
NOVELTY_AXIS: >-
  Exact theta-dependent finite reweighting, quantitative all-k conditional
  coupling obstruction, and same-visible-law hidden-spin exclusion.
LITERATURE_PRIORITY_CLAIM: NOT_MADE
```

## 13. Закрытие опыта и единственная директива приёма

**P_LIMIT — подтверждено:** выполнены (9)–(13) для исправленных законов.

**P_EDGE — подтверждено:** строгая исходная верхняя оценка (16), а не сбой достаточной оценки, исключает ферромагнитность этих законов.

**Что стало точнее:** цена вставки полной \(\Phi\) выражена точным четырёхконфигурационным дефектом. Сходимость исправленной семьи больше не смешивается с Lee–Yang-свойством начальной семьи. Скрытые положительные связи не могут реализовать тот же совместный закон.

**Что не стало меньше:** неизвестность существования другой GS-реализации \(p\), all-order знака или RH. Положительный исходный механизм для конечного потребителя не получен. Ни две скалярные вогнутости, ни additive TN, ни положительность \(\mathcal R_k\) не используются как его замена.

**Не повторять:** тот же точный entropy-fit (6) с надеждой, что увеличение числа спинов исправит ферромагнитность; переставлять доказанную сходимость (6) на другую семью (4); добавлять скрытые ферромагнитные спины при требовании сохранить буквально тот же видимый закон; называть этот kill доказательством \(p\notin GS\).

**Предлагаемый source-sign счёт:** \(2\to3\). Он меняется только независимым приёмом. После трёх no-delta требуется возврат к владельцу; автоматическое продолжение Hankel/Stein или новый список контрольных примеров этим ответом не разрешается.

**Одна CODEX DIRECTIVE:** провести независимый PAPER-приём именно данного артефакта: проверить теорему A, полный бюджет (18)–(22), маргинализационную лемму (24) и область (25); затем воспроизвести Appendix B без theta-вычислений. При успехе принять только `KILL_EXACT_THETA_ENTROPY_BINOMIAL_JOINT_LIFT`, сохраняя `GENERAL_PHI_GS_REALIZATION_OPEN`. При ошибке вернуть первую неверную формулу и её область. Не запускать второй конструктивный опыт в этой транзакции.

Записей в GitHub, очереди, runtime, счётчиках и Lean не выполнялось. Production admission и RH-claim отсутствуют.

```yaml
STRATEGY_MEMORY:
  iteration: REQ-2026-09-12-LYGSPHI
  target: source-derived nonnegative pair-spin realization of Phi/Z
  status: FATAL_FOR_EXACT_JOINT_CONSTRUCTION_ONLY
  failed_strategy: exact theta reweighting of a critical binomial block
  cognitive_operator_used: BOUNDARY_CASE
  new_gap_name: ADMISSIBLE_FERROMAGNETIC_MAGNETIZATION_APPROXIMATION_NOT_EXACT_MICROSTATE_FIT
  invariant_learned: the field transform and the Lee-Yang hypothesis must belong to the same law
  forbidden_future_move: transfer Lee-Yang from the precursor after an unverified source tilt
  next_decisive_test: independent review of the completed construction-specific kill
```

## Приложение A. Побайтовый манифест

| Файл внутри пакета | Байты | LF | SHA-256 | Git blob |
|---|---:|---:|---|---|
| `docs/Codex/REPORT_2026-09-12_PHYSICS_BROTHER_LEE_YANG.md` | 13048 | 250 | `cbfa295fa3778dbf2375a5892b3caad0d4b381e3784727bcc187dd909764d5ed` | `2d6a33f184385689e7a5535dbae11a21cc6f3ca6` |
| `docs/Codex/REPORT_2026-09-12_ALL_ODD_TO_RH.md` | 14112 | 308 | `760fd70fd1e6c3f5b07f8c6eced03bf3f2dfb69698cfb67f597ead219ff8940a` | `42d3297731443474b08f2010d6d00d1f1d37c64b` |
| `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md` | 37796 | 467 | `14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc` | `de9578084446baecfbb2a316d7bda3da817c8c01` |
| `docs/Codex/REPORT_2026-09-12_SOURCE_MOMENT_HANKEL_INTERFACE.md` | 8910 | 205 | `f549fb4fe3990bbc360cb39a657f713ee5576259f997f403938cfc6ed7280aa1` | `3f60792d70f1d06e6454ef3b60ed96bc698a1280` |

Все четыре декодированных файла — UTF-8, конечный LF, без CR. Проверка рамок ниже не читает рекурсивный архив.

## Приложение B. Точный исполненный код и буквальный stdout

Это проверка входных байтов, девяти рациональных сравнений и знака калибровочных спиновых моделей. Она **не** вычисляет исходные theta-значения, не заменяет доказательства теорем A–C и не сертифицирует RH. Весь математический бюджет построен до этой проверки; код лишь воспроизводит его точную арифметику.

Сохрани следующий блок как `verify_lyg.py`. В команде `python verify_lyg.py {request_path}` подставь вместо `{request_path}` путь к авторитетному TXT. Например, выполненная команда:

```bash
python /mnt/data/lyg_work/verify_lyg.py /mnt/data/PROSHKA_REQUEST_GOAL058_LYGSPHI_2026-09-12.txt
```

SHA-256 исполненного Python: `7745fa643285580ebc33695e34f437870df3745d9a97c2f56a5b408cf818dc35`.

```python
#!/usr/bin/env python3
"""Exact intake and rational checks for the LYGSPHI construction test.
No theta quadrature, root search, or finite-Hankel computation is performed.
Usage: python verify_lyg.py /path/to/PROSHKA_REQUEST_GOAL058_LYGSPHI_2026-09-12.txt
"""
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import hashlib
import re
import sys

EXPECTED_SHA = '32d75bc0235c8aaa48c326e240b5e1123d914d0caf8ea568a86402adb0ae2e71'
EXPECTED_BLOB = '1d8d84e660e4cb503ce44dfe86ba0f661160e33b'


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def intake(path: Path) -> None:
    data = path.read_bytes()
    data.decode('utf-8', errors='strict')
    assert len(data) == 89217
    assert data.count(b'\n') == 1384 and data.count(b'\r') == 0
    assert data.endswith(b'\n')
    assert hashlib.sha256(data).hexdigest() == EXPECTED_SHA
    assert git_blob(data) == EXPECTED_BLOB
    print('REQUEST bytes=89217 LF=1384 CR=0 final_LF=true HASHES=PASS')
    lines = data.splitlines(keepends=True)
    i, count = 0, 0
    header = re.compile(rb'===== FILE (.+) BYTES (\d+) LF (\d+) FINAL_LF true SHA256 ([0-9a-f]{64}) =====\n')
    while i < len(lines):
        match = header.fullmatch(lines[i])
        if match is None:
            i += 1
            continue
        name = match.group(1).decode('utf-8')
        nbytes, nlines = int(match.group(2)), int(match.group(3))
        block = lines[i + 1:i + 1 + nlines]
        assert len(block) == nlines and all(s.startswith(b'| ') for s in block)
        payload = b''.join(s[2:] for s in block)
        payload.decode('utf-8', errors='strict')
        assert len(payload) == nbytes and payload.count(b'\n') == nlines
        assert payload.endswith(b'\n') and b'\r' not in payload
        sha = hashlib.sha256(payload).hexdigest()
        assert sha == match.group(4).decode()
        assert lines[i + 1 + nlines] == ('===== END FILE ' + name + ' =====\n').encode()
        count += 1
        print(f'FRAME {count} bytes={nbytes} LF={nlines} sha256={sha} blob={git_blob(payload)} PASS')
        i += nlines + 2
    assert count == 4
    print('FRAMES count=4 PASS')


def weights(bases: dict[tuple[int, int], Q]) -> dict[tuple[int, ...], Q]:
    out = {}
    for sig in product((-1, 1), repeat=3):
        w = Q(1)
        for (i, j), base in bases.items():
            assert base > 0
            w *= base ** (sig[i] * sig[j])
        out[sig] = w
    return out


def odds(w: dict[tuple[int, ...], Q], z: int) -> Q:
    return w[(1, 1, z)] * w[(-1, -1, z)] / (w[(1, -1, z)] * w[(-1, 1, z)])


def exact_checks() -> None:
    neutral = weights({})
    ferro = weights({(0, 1): Q(2), (0, 2): Q(3), (1, 2): Q(5)})
    anti = weights({(0, 1): Q(1, 2), (0, 2): Q(3), (1, 2): Q(5)})
    for z in (-1, 1):
        assert odds(neutral, z) == 1
        assert odds(ferro, z) == 16
        assert odds(anti, z) == Q(1, 16)
    print('PLANT neutral odds=1; ferromagnetic odds=16; antiferromagnetic odds=1/16 PASS')
    hidden = weights({(0, 2): Q(2), (1, 2): Q(3)})
    marginal = {(a, b): sum((hidden[(a, b, z)] for z in (-1, 1)), Q(0))
                for a, b in product((-1, 1), repeat=2)}
    hidden_odds = marginal[(1, 1)] * marginal[(-1, -1)] / (marginal[(1, -1)] * marginal[(-1, 1)])
    assert hidden_odds == Q(1369, 169) > 1
    print(f'PLANT hidden-ferromagnet marginal odds={hidden_odds} PASS')
    k, n, delta = 4, 4**4, Q(1, 4**3)
    nodes = (Q(k), Q(k) - 2 * delta, Q(k) - 4 * delta)
    assert nodes[0] + nodes[2] == 2 * nodes[1]
    entropy = Q(comb(n, n-1)**2, comb(n, n)*comb(n, n-2))
    assert entropy == Q(2*n, n-1) == Q(512, 255)
    print(f'EDGE k=4 n=256 delta={delta} nodes={nodes[0]},{nodes[1]},{nodes[2]} entropy={entropy} PASS')
    checks = [
        ('theta_geometric_ratio', Q(81,16) * Q(1,2)**500, '<', Q(1,2)),
        ('theta_tail', Q(32) * Q(1,2)**300, '<', Q(1,100)),
        ('H_lower', Q(197,200), '>', Q(9,10)),
        ('H_upper', Q(101,100), '<', Q(11,10)),
        ('smallest_argument_guard', Q(3)*Q(2)**6, '>', Q(100)),
        ('full_prefactor', Q(512,255)*Q(11,9)**2, '<', Q(4)),
        ('source_exponent_lower', Q(48)*Q(8,3)**7/Q(4)**6, '>', Q(11)),
        ('odds_upper', Q(4)*Q(3,8)**11, '<', Q(1,10000)),
        ('robust_relative_repair', Q(10)**4*Q(4)*Q(3,8)**11, '<', Q(1)),
    ]
    for name, lhs, relation, rhs in checks:
        assert (lhs < rhs) if relation == '<' else (lhs > rhs)
        # Huge fractions are validated but not dumped: the exact expression is in the source.
        if name not in ('theta_geometric_ratio', 'theta_tail'):
            print(f'RATIONAL {name}: {lhs} {relation} {rhs} PASS')
        else:
            print(f'RATIONAL {name}: PASS')
    print('RATIONAL_CHECKS count=9 PASS')
    print('SOURCE_EVALUATIONS=0; QUADRATURES=0; HANKEL_TESTS=0; LEAN_RUNS=0')
    print('PROOF_ROLE=exact_arithmetic_and_plants_only; analytic_proof_requires_independent_review')


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit('Usage: python verify_lyg.py /path/to/PROSHKA_REQUEST_GOAL058_LYGSPHI_2026-09-12.txt')
    path = Path(sys.argv[1])
    if not path.is_file():
        raise FileNotFoundError(path)
    intake(path)
    exact_checks()


if __name__ == '__main__':
    main()
```

Буквальный stdout: 1461 UTF-8 байт, 21 LF, конечный LF. SHA-256: `1b5272ef9a794a3e0286864adf3d06e8edef114eece85b293df4c767c668789b`.

```text
REQUEST bytes=89217 LF=1384 CR=0 final_LF=true HASHES=PASS
FRAME 1 bytes=13048 LF=250 sha256=cbfa295fa3778dbf2375a5892b3caad0d4b381e3784727bcc187dd909764d5ed blob=2d6a33f184385689e7a5535dbae11a21cc6f3ca6 PASS
FRAME 2 bytes=14112 LF=308 sha256=760fd70fd1e6c3f5b07f8c6eced03bf3f2dfb69698cfb67f597ead219ff8940a blob=42d3297731443474b08f2010d6d00d1f1d37c64b PASS
FRAME 3 bytes=37796 LF=467 sha256=14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc blob=de9578084446baecfbb2a316d7bda3da817c8c01 PASS
FRAME 4 bytes=8910 LF=205 sha256=f549fb4fe3990bbc360cb39a657f713ee5576259f997f403938cfc6ed7280aa1 blob=3f60792d70f1d06e6454ef3b60ed96bc698a1280 PASS
FRAMES count=4 PASS
PLANT neutral odds=1; ferromagnetic odds=16; antiferromagnetic odds=1/16 PASS
PLANT hidden-ferromagnet marginal odds=1369/169 PASS
EDGE k=4 n=256 delta=1/64 nodes=4,127/32,63/16 entropy=512/255 PASS
RATIONAL theta_geometric_ratio: PASS
RATIONAL theta_tail: PASS
RATIONAL H_lower: 197/200 > 9/10 PASS
RATIONAL H_upper: 101/100 < 11/10 PASS
RATIONAL smallest_argument_guard: 192 > 100 PASS
RATIONAL full_prefactor: 61952/20655 < 4 PASS
RATIONAL source_exponent_lower: 8192/729 > 11 PASS
RATIONAL odds_upper: 177147/2147483648 < 1/10000 PASS
RATIONAL robust_relative_repair: 110716875/134217728 < 1 PASS
RATIONAL_CHECKS count=9 PASS
SOURCE_EVALUATIONS=0; QUADRATURES=0; HANKEL_TESTS=0; LEAN_RUNS=0
PROOF_ROLE=exact_arithmetic_and_plants_only; analytic_proof_requires_independent_review
```

## Итоговый operative verdict

**KILL_NAMED_PHI_SPIN_CONSTRUCTION.** Точный источник-зависимый entropy-corrected binomial lift имеет весь нужный вероятностный предел, но строго нарушает необходимую парную ферромагнитность. Общая конструкция Griffiths–Simon для \(\Phi/Z\) остаётся открытой. Новый полный исходный знак не получен; предлагаемый счёт — **2 → 3**, только после независимого приёма.
