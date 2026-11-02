# STATUS: TRY_NOESCAPE_F_ONLY_SPECTRAL_GUARDS
```yaml
OPERATIVE_CLASS: TRY_NOESCAPE_F_ONLY_SPECTRAL_GUARDS
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_F_ONLY_NOESCAPE_AND_RELATIVE_EXTERIOR_REQUEST
SOURCE_REPOSITORY: Malaeu/chen_q3
SOURCE_BRANCH: rh_clean
SOURCE_COMMIT: e9d36a8245a79a6b0436d52719828024f202ec61
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md
SOURCE_SHA256: fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded
SOURCE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
SOURCE_BYTES: 64077
SOURCE_LF_LINES: 1084
SOURCE_HASH_CHECK: MATCH_LOCAL_SHA256_AND_REMOTE_GIT_BLOB
CARRIER: LITERAL_CCM_EVEN_N_EQUALS_M_L_EQUALS_LOG_M
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
REQUESTED_COFINAL_F_ONLY_BOUND: NOT_PROVED
REQUESTED_UNIFORM_COORDINATEWISE_X_OVER_F: NOT_PROVED
REQUESTED_ASSERTIONS_REFUTED_FOR_LITERAL_CCM: false
M16_D_EXT: DIAGNOSTIC_CLOSURE_X_EQUALS_T_MINUS_F_NOT_INDEPENDENT_X
M16_REPORTED_LEVELS: [0, 1, 2, 3]
NEW_EXPLICIT_SOURCE_RESULT: HIGH_LOW_EVEN_ROW_AND_ALL_MODE_TAIL_ENVELOPE
POLYNOMIAL_HIGH_ABSOLUTE_ENERGY_F_SUM: SUPERPOLYNOMIALLY_SMALL_USING_PINNED_SUPPLIERS
LOW_CLUSTER_STRICT_MARGIN: UNPAID
ZERO_MODES_AND_BOTTOM_MULTIPLICITY: RETAINED
RH_PROVED: false
T_PROVED: false
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
SOURCE_SIGN_PROGRESS: NO_NEW_COFINAL_STRICT_MARGIN
EXACT_ALGEBRA_GROUPS_EXECUTED: 7
NEW_LITERAL_CCM_NUMERICAL_SCAN: false
INDEPENDENT_X_QUADRATURE_EXECUTED: false
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
```

## 0. Результат

**Две запрошенные оценки на неограниченной подпоследовательности не доказаны.** Ниже выполнена исходниковая попытка: получены явная формула всех high/low-строк, строгий остаток бесконечной суммы F, полный перенос относительной ошибки и отделение всех уровней выше любого фиксированного полиномиального порога. Не доказаны строгий запас ниже единицы в низком кластере и равномерное отсутствие опасного сокращения в координатах F.

Это не опровержение целевых утверждений для CCM. То, что их совместное доказательство даст RH, является целью, а не возражением. Однако две конечные диагностические точки не заменяют этот квантор.

Проверка данных меняет ровно область доступного свидетельства: D_ext в указанном пакете означает |X|/|F+X|, а не |X|/|F|; X вычислен как T−F. Независимого расчёта внешней формы там нет. У m16 опубликованы только четыре уровня, включая bottom. Значение 9.47626e−5 относится к i=1, а не к максимуму по всем возбуждённым уровням.

## 1. Source lock и реестр

S1: полный локальный NOESCAPE имеет 64077 байт, 1084 LF и SHA-256 из header. Пересчитанный Git blob совпал с fetch_file на закреплённом коммите. Использованы §1, L1–L3, L6–L11: определения, residual, точная F+X-идентичность и внешний envelope. Это унаследованные PAPER-поставщики; нового независимого аудита всей цепочки не заявляется.

S2: `docs/routeB_bus/thetagrade_2026-10-28/m16_2026-11-02/RESULT.md`, blob `500bf54a01b61ef3d13a84c1497aa30ea8026808`: явная маркировка DIAGNOSTIC_NEVER_A_PROOF, замыкание X=T−F, отсутствие tail-enclosure.

S3: та же папка, `leakage_split_m16_dps100_gl128.jsonl`, blob `8d9862c61b6b9fd1a28c88d769ecab1ede9920b9`: четыре словаря i=0,1,2,3, Z и частичные F.

S4: `docs/routeB_bus/thetagrade_2026-10-28/leakage_split_shared_gl.py`, blob `d983881820ffc8bd7eb304f2565370c6fbc4f8f5`: прочитан полностью. Код явно задаёт `X=T-F`, `D_ext=abs(X)/abs(T)`, цикл `range(4)` и конечный leakage-cutoff. Дополнительные моды не входят в eigenproblem.

S5: `m16_2026-11-02/spotcheck.json`, blob `18f169b606335b85ec4385fffd11a3f45e5a01cd`, и `source_hashes.json`, blob `10a8da2b5c0dfc942af0e16edaca8c89cf260077`: дополнительные floating-сверки коэффициентов/моментов и происхождение кода. Они не являются независимым сертификатом X или всех собственных пар.

Все S1–S5 закреплены на SOURCE_COMMIT. Значение D_ext(m8)=0.192 берётся только из сообщения владельца; отдельный m8-файл в этой сессии не прочитан. Протокол получен с rh_clean, включая конец, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`.

Никакая quasi-RH предпосылка, новый zero-location supplier или результат MUK в доказательства ниже не импортируется. Код прежних диагностик не запускался. Выполнены собственные точные проверки Appendix A и арифметика округлённых данных.

## 2. Точные цели и безопасный перенос

**[ABSTRACT | PAPER; definitions and pinned identities.]** Пусть A_m — исходный чётный блок, L=log m, N=m. Выбираем ортонормированный вещественный eigenbasis v_i, включая один выбранный bottom v_0; простоту не предполагаем. Положим
\[
p_m=P_mh,\quad Z_m=\|p_m\|>0,\quad u_m=p_m/Z_m,\quad
 a_i=\langle u_m,v_i\rangle,
\quad\mathcal I_m=\{i\ge1:\lambda_i\ne0\},
\quad z_m=\sum_{i\ge1,\lambda_i=0}|a_i|^2.
\]
Из S1 (4.1),(4.8) точно
\[
F_i+X_i=-Z_m\lambda_i a_i. \tag{2.1}
\]
Определим
\[
S_m^F=\sum_{i\in\mathcal I_m}\frac{|F_i|^2}{Z_m^2\lambda_i^2}+z_m,
\quad S_m^T=1-|a_0|^2
=\sum_{i\in\mathcal I_m}\frac{|F_i+X_i|^2}{Z_m^2\lambda_i^2}+z_m.
\tag{2.2}
\]
Требуется одна неограниченная семья, на которой S_m^F<=c<1, и относительный bound с eta_m→0. Ниже для достаточности достаточно относительного bound на I_m; требование ещё и для остальных индексов сильнее.

### Лемма 1. При доказанном относительном bound удаление X законно

**[COFINAL_FAMILY | PAPER; implication, not its source hypotheses.]** Если
\[
|X_i|\le\eta_m|F_i|\quad(i\in\mathcal I_m),\qquad 0\le\eta_m<1,
\]
то
\[
(1-\eta_m)^2(S_m^F-z_m)+z_m
\le S_m^T\le
(1+\eta_m)^2(S_m^F-z_m)+z_m. \tag{2.3}
\]
Доказательство — обе треугольные оценки для каждой F_i+X_i, затем суммирование. Знаковые сокращения не объявляются отсутствующими: их влияние ограничено именно предпосылкой eta.

Следовательно, S_m^F<=c<1 и eta_m→0 дают S_m^T<=c'<1 на хвосте той же семьи: выбираем eta_* с (1+eta_*)²c<1. По S1 L8,L6 это доказывает T для span{h}, затем RH.

Обратно, при eta_m→0 доказанный строгий bound S_m^T<=d<1 даёт S_m^F<=d/(1-eta_m)²<1 на хвосте. Это условная эквивалентность двух leakage-входов при относительном supplier, **не утверждение T⇐RH**.

### Нули и кратность

Если F_i=0, относительное условие требует X_i=0; это нельзя проверять делением на нулевой интервал. Если lambda_i=0 и относительное условие требуется также на этом индексе, (2.1) и eta_m<1 вынуждают F_i=X_i=0. Но z_m от этого не исчезает.

При кратности coordinatewise-условие зависит от выбора базиса внутри собственного пространства. Не утверждается его независимость от такого выбора. Для версии «все единичные направления одного eigenspace» понадобилось бы неравенство двух rank-one форм; оно существенно сильнее.

### Лемма 2. Более слабый достаточный контроль внешней ошибки

**[ABSTRACT | PAPER.]** Пусть b_m,x_m — Riesz-векторы F_m,X_m в carrier. Тогда
\[
b_m+x_m=-A_mp_m. \tag{2.4}
\]
Пусть E_m^X — inverse-weighted excited norm:
\[
E_m^X=\frac1{Z_m}
\left(\sum_{i\in\mathcal I_m}\frac{|X_i|^2}{\lambda_i^2}\right)^{1/2}.
\]
Точно
\[
\boxed{|\sqrt{S_m^F}-\sqrt{1-|a_0|^2}|\le E_m^X.} \tag{2.5}
\]
Доказательство: применить обратное треугольное неравенство к векторам с координатами F_i/(Z lambda_i), (F_i+X_i)/(Z lambda_i) и одной общей дополнительной координатой sqrt(z_m).

E_m^X=o(1) было бы достаточным для переноса строгого запаса; это слабее требуемой coordinatewise-оценки. Оно здесь не получено. Нельзя переименовать его в уже доказанный внешний envelope.

## 3. Выполненная исходниковая попытка: все high/low-строки

Работаем в точном вещественном чётном базисе
\[
e_{j,L}(x)=\frac{d_j}{\sqrt L}\cos(2\pi j(x/L+1/2))\mathbf1_{[-L/2,L/2]},
\quad d_0=1,\ d_j=\sqrt2\ (j\ge1).
\]
Высокие e_n, n>m, используются **только в F**, не добавляются к A_m. Обозначим
\[
S_\Lambda(m)=\sum_{2\le k\le m}\frac{\Lambda(k)}{\sqrt k},\quad
\Omega_j=2\pi j/L,
\]
\[
\beta_j=\int_0^L j(s)\sin(\Omega_j s)ds
+\sum_{2\le k\le m}\frac{\Lambda(k)}{\sqrt k}\sin(\Omega_j\log k),
\quad\beta_0=0,
\]
\[
u_j=\langle p,e_{j,L}\rangle
=\frac{4\sqrt2\,d_j L^{3/2}\sinh(L/4)}{L^2+16\pi^2j^2},\qquad
P_L=\|p\mathbf1_{I_L}\|_2=\sqrt{L+2\sinh(L/2)}.
\]

### Лемма 3. Точный source row и его uniform envelope

**[ABSTRACT | PAPER; literal source, every m>=2 and n>m.]** Для 0<=j<=m:
\[
\boxed{\mathfrak k(e_n,e_j)=u_nu_j+
\frac{d_nd_j}{\pi}\frac{n\beta_n-j\beta_j}{n^2-j^2}.} \tag{3.1}
\]
Доказательство. Чётная компрессия корреляционного ядра S1/S4 даёт
\[
Q_{e_n,e_j}(s)=
\frac{d_nd_j[j\sin(\Omega_js)-n\sin(\Omega_ns)]}{\pi(n^2-j^2)}.
\]
Это включает j=0. Нормовый диагональный член равен нулю по ортогональности. Отрицательная arch/prime-корреляция даёт второе слагаемое (3.1), чётный полюс — u_nu_j. При log k>L корреляция нулевая из-за поддержки, а при log k=L она также нулевая. Это не усечение внешнего X.

Для j>=1 точный arch-синусный момент имеет положительный ряд
\[
\int_0^L j(s)\sin(\Omega_js)ds
=\sum_{r\ge0}\frac{\Omega_j(1-e^{-(2r+1/2)L})}{(2r+1/2)^2+\Omega_j^2}.
\tag{3.2}
\]
Он следует из геометрического ряда для j(s), sin(Omega_j L)=0 и cos(Omega_j L)=1. Перестановка законна: j(s)|sin(Omega_j s)| интегрируемо около нуля.
Монотонная интегральная оценка по r даёт
\[
0\le\int_0^L j(s)\sin(\Omega_js)ds\le1+\pi/4,
\quad |\beta_j|\le B_m:=1+\pi/4+S_\Lambda(m). \tag{3.3}
\]
Действительно, первое слагаемое не больше 1, интеграл остальных не больше pi/4.

Пусть r_n=(k(e_n,e_j))_{j=0}^m. Из (3.1), n>j и суммы d_j²=2m+1:
\[
\|r_n\|_2\le\frac{A_m^{\rm row}}{n^2}
+\frac{B_m^{\rm row}}{n-m}, \tag{3.4}
\]
\[
A_m^{\rm row}=\frac{L^{3/2}\sinh(L/4)P_L}{2\pi^2},
\qquad B_m^{\rm row}=\frac{\sqrt{2(2m+1)}B_m}{\pi}.
\]
Здесь используется (n+j)/(n²−j²)=1/(n−j) и ||(u_j)_(j<=m)||<=P_L. Все константы — явные исходные величины, не eigenvalue budgets. ∎

### Лемма 4. Строгий остаток бесконечной суммы F

**[ABSTRACT | PAPER; all high modes retained.]** Riesz-вектор F равен
\[
b_m=\sqrt{2/L}\sum_{n>m}(-1)^nH(\Omega_n)r_n. \tag{3.5}
\]
Для целого R>=2m и p>=1 его усечение b_m^[R] удовлетворяет
\[
\boxed{\|b_m-b_m^{[R]}\|_2\le\varepsilon_F(m,R,p)}
\]
\[
\varepsilon_F=
\sqrt{2/L}\,H_p\left(\frac L{2\pi}\right)^p
\left[\frac{A_m^{\rm row}}{(p+1)R^{p+1}}
+\frac{2B_m^{\rm row}}{pR^p}\right],
\quad H_p=\|h^{(p)}\|_1. \tag{3.6}
\]
Доказательство. Интегрирование по частям на всей прямой даёт |H(Omega_n)|<=H_p(L/(2pi n))^p. Для n>R>=2m имеем 1/(n−m)<=2/n. Суммы n^(−p−2),n^(−p−1) ограничены соответствующими интегралами от R. Это доказывает (3.6), а также абсолютную сходимость (3.5). В частности, каждый F_i имеет ту же абсолютную tail-цену.

H_p можно ограничить без неизвестной константы. Положим
\[
P_0(y)=16y^2-24y,\quad
P_{p+1}(y)=\tfrac12P_p(y)+2y(P_p'(y)-P_p(y)),
\quad P_p(y)=\sum_k c_{p,k}y^k.
\]
Дифференцирование theta-ряда и y=pi n²e^(2x) дают
\[
H_p\le\sum_{n\ge1}(\pi n^2)^{-1/4}
\sum_k|c_{p,k}|\,\Gamma(k+1/4,\pi n^2).
\]
Например, полностью конечный выбор:
\[
\boxed{H_p\le
\frac{\pi^{-1/4}e^{-\pi/2}}{1-e^{-3\pi/2}}
\sum_k|c_{p,k}|2^{k+1/4}\Gamma(k+1/4).} \tag{3.7}
\]
Для проверки: e^(−y)<=e^(−pi n²/2)e^(−y/2), а n²>=1+3(n−1). Оценка грубая, но явная и независимая от m,R и выбранного eigenvector. ∎

**Что попытка не дала.** (3.1),(3.5) сохраняют знаки и всю недиагональную структуру, но H(Omega_n), (-1)^n и eigenvector coordinates сокращаются. (3.6) — upper для хвоста, не lower для |F_i|. Прибавлять большие слагаемые по модулю для получения нижней границы нельзя.

## 4. Что можно доказать кофинально без нового спектрального входа

**[COFINAL_FAMILY | PAPER; consequence of pinned S1 L1,L11.]** Обозначим через Xcal_m явный envelope S1 (4.13)–(4.14). Он сохраняет h_out, периодизацию W, P_mW, оба края, полюс и все внешние степени простых. В частности,
\[
\|x_m\|\le\mathcal X_m\le C m^4(1+\log m)^2e^{-\pi m}.
\]
Также S1 даёт
\[
\delta_m:=\|A_mu_m\|=O_A(m^{-A})\quad\text{для каждого фиксированного A},
\qquad Z_m\to\|h\|>0.
\]
Из (2.4) получаем без деления на отдельные неизвестные F_i:
\[
\|b_m\|\le Z_m\delta_m+\mathcal X_m.
\]
Для любого rho>0:
\[
\boxed{
\sum_{\substack{i\ge1\\|\lambda_i|\ge\rho}}
\frac{|F_i|^2}{Z_m^2\lambda_i^2}
\le\frac{(\delta_m+\mathcal X_m/Z_m)^2}{\rho^2},}
\tag{4.1}
\]
\[
\boxed{
\frac1{Z_m}\left(\sum_{\substack{i\ge1\\|\lambda_i|\ge\rho}}
\frac{|X_i|^2}{\lambda_i^2}\right)^{1/2}
\le\frac{\mathcal X_m}{Z_m\rho}.}
\tag{4.2}
\]
Это Parseval и |lambda_i|>=rho, не предположение о знаке eigenvalues.

При rho=m^(−B), B>0 фиксировано, обе правые части убывают быстрее любой фиксированной обратной степени m. Следовательно для любого A>0
\[
S_m^F=
\sum_{\substack{i\ge1\\0<|\lambda_i|<m^{-B}}}
\frac{|F_i|^2}{Z_m^2\lambda_i^2}+z_m+O_{A,B}(m^{-A}). \tag{4.3}
\]
**Это закрывает high-absolute-energy часть, но не строгий запас.** S1 L3 одновременно говорит, что число уровней в полиномиальной полосе около нуля неограниченно растёт. Поэтому несколько первых сохранённых уровней не покрывают оставшийся кластер кофинально.

Для полной inverse-weighted ошибки известен лишь
\[
E_m^X\le\frac{\mathcal X_m}{Z_m g_m},\quad
 g_m=\min_{i\in\mathcal I_m}|\lambda_i|,
\tag{4.4}
\]
если I_m непусто; при пустом I_m ошибка нулевая. Нижняя граница g_m, делающая (4.4) малой, не поставлена. Она достаточна, но не объявляется обязательной: directional cancellation может дать более слабый рабочий интерфейс.

## 5. Точная цена относительного X/F и конечные данные

**[ABSTRACT | PAPER.]** Если для отдельного уровня доказано
\[
D_i:=\frac{|X_i|}{|F_i+X_i|}\le d<1,
\]
то
\[
\boxed{\frac{|X_i|}{|F_i|}\le\frac d{1-d}.} \tag{5.1}
\]
Это следует из |F_i|>=|F_i+X_i|−|X_i|. Ненулевой denominator и независимый upper для X обязательны.

Для owner-reported m8, d=0.192, формальная цена d/(1−d)=0.2376237624. Для опубликованного m16 i=1 она равна 9.47715808e−5. Это только пересчёт диагностического отношения, **не сертификация** обеих строк и не eta_m→0.

Из округлённых S3 вычислены следующие диагностические числа:

| i | |F_i/(Z lambda_i)|² | |X_closure/F_i| |
|---|---:|---:|
| 1 | 0.00155905829046 | 9.47536495e−5 |
| 2 | 0.00000371353433807 | 1.56223099e−5 |
| 3 | 0.000000011801648725 | 3.24059851e−6 |

Подытог i=1,2,3 равен примерно 0.00156278362644. Это **не полная сумма m16**: i=4,...,16, точный статус нулевых уровней и error-enclosures не предоставлены этим JSON. i=0 не входит в целевую сумму. В RESULT.md явно записаны отсутствие rigorous F-tail enclosure и нестабильность отдельных G-partials.

Формула (3.6) позволяет оплатить бесконечный F-хвост, но точный eigenbasis/его ошибки, нижние границы |lambda_i|, Z и независимая физическая X-квадратура — отдельные входы. X=T−F не является независимой проверкой S1 (4.8).

### Точный конечный certification contract

При сертифицированных enclosures |F_i−Fhat_i|<=r_i+epsilon_F, |X_i|<=x_i^+, |lambda_i|>=ell_i>0, Z>=Z_->0:
\[
f_i^-=(|\widehat F_i|-r_i-\varepsilon_F)_+,
\quad \eta_m^+ =\max_i\frac{x_i^+}{f_i^-},
\]
\[
(S_m^F)^+=z_m^++
\sum_i\frac{(|\widehat F_i|+r_i+\varepsilon_F)^2}{Z_-^2\ell_i^2}.
\tag{5.2}
\]
Радиусы r_i должны включать ошибки коэффициентов и eigenvectors, не только quadrature. Если f_i^-=0, результат zero-consistent, а не PASS: нужен refinement либо доказательство F_i=X_i=0. Нельзя удалить уровень с lambda-interval, содержащим ноль, без точного kernel-анализа. Неперечисленные уровни можно оплачивать (4.1) только после доказанной спектральной классификации по порогу.

## 6. Контроли, которые запрещают ложное закрытие

### Лемма 5. Абсолютно малый X не позволяет выкинуть его

**[ABSTRACT | PAPER; not CCM.]** Пусть epsilon_m=2^(−m²), Z=1,
\[
A_m=\operatorname{diag}(\epsilon_m^2,\epsilon_m),\quad u=e_1,
\quad b_m=\epsilon_m^2e_1,\quad
x_m=-(\epsilon_m+\epsilon_m^2)e_1.
\]
Нижний уровень простой, остаток ||A_mu||=epsilon_m, b_m+x_m=−A_mu и ||x_m||<=2epsilon_m. Последняя величина в конце меньше любого C m^4(1+log m)²e^(−pi m) с C>0. Но
\[
S_m^F=\epsilon_m^2\to0,\quad S_m^T=1,\quad
|X_1/F_1|=\epsilon_m^{-1}+1\to\infty.
\tag{6.1}
\]
Таким образом даже точная closure-идентичность, сверхмалая residual и сверхмалая абсолютная внешняя норма не оправдывают удаление X. Это опровергает только общий shortcut; у матрицы нет буквальной арифметики CCM.

Обратный контроль: при u=e_1, lambda_1=epsilon−epsilon³, lambda_0=lambda_1/2, F_1=−epsilon, X_1=epsilon³ имеем |X/F|=epsilon²→0, но S_F=(1−epsilon²)^(−2)>1 и S_T=1. Относительная ошибка сама по себе также не поставляет строгий gap.

## 7. Точная граница попытки и следующий дискриминатор

**[COFINAL_FAMILY | CONDITIONAL; source hypotheses NOT proved.]** После оплаченной (4.3) требуется на одной неограниченной семье:
\[
\sum_{\substack{i\ge1\\0<|\lambda_i|<m^{-B}}}
\frac{|F_i|^2}{Z_m^2\lambda_i^2}+z_m\le c_0<1,
\tag{7.1}
\]
и отдельно
\[
\eta_m^*:=\max_{i\in\mathcal I_m}\frac{|X_i|}{|F_i|}\longrightarrow0.
\tag{7.2}
\]
В (7.2) 0/0 означает 0 только после точного общего зануления; X_i!=0,F_i=0 означает infinity. Эти условия не следуют из (3.6) или двух D_ext. Не установлены ни их истинность, ни их ложность для литерального семейства.

Два допустимых представления, без обязательного усиления цели:

| Представление | Решающий объект | Сила / стоимость |
|---|---|---|
| Прямое подписанное high/low | (3.1),(3.5) и независимый внешний функционал S1 (4.12), с lower для каждой нужной F-координаты | Высокая для запрошенного eta / средняя конечная, высокая кофинальная |
| Сжатая inverse-square метрика | E_m^X и low-cluster F-norm, без требования coordinatewise domination | Достаточна для потребителя и слабее (7.2) / не требует inverse на полном пространстве, но low spectrum остаётся неоплаченным |

Zero-consistent DISCRIMINATOR: для F_i-interval около нуля требуется либо направленная нижняя граница полной знаковой (3.5), либо точное совместное F_i=X_i=0. Увеличение precision без аналитического F-tail radius не закрывает этот тест.

Единственная следующая CODEX DIRECTIVE: независимо построить полный finite m16 low-cluster F/X-сертификат по (5.2), X вычислять из h_out и periodization, не как T−F; отсутствующие уровни и kernel включить. Это тест поставщика, **не замена запрошенного кофинального доказательства**. Успех finite gate не повышает (7.1),(7.2) до теоремы.

### Closeout и dependency ledger

- Scope/verifier: exact algebra — ABSTRACT/PAPER; high/low formulas — literal-source PAPER for every finite m; (4.1)–(4.3) — COFINAL_FAMILY/PAPER using S1 suppliers; (7.1)–(7.2) — COFINAL_FAMILY/CONDITIONAL, not supplied.
- DOWNSTREAM_CONSUMER: original one-jet NOESCAPE T, then RH by S1.
- ACTUAL_CONSUMER_REQUIREMENT: complete F+X inverse-weighted excited mass bounded below 1 with z_m included.
- ORIGINAL_REQUESTED_OBJECT: F-only strict bound plus coordinatewise eta_m→0.
- ORIGINAL_OBJECT_IS: sufficiency proved; necessity for RH NOT_ESTABLISHED. Coordinatewise eta is not necessary for the weaker aggregate interface.
- FAILURE_TYPE: NO_DERIVATION of cofinal low-cluster margin and relative source comparison.
- EPISTEMIC_STATUS: RESEARCH_DEBT, not route death.
- REOPEN_TRIGGER: source theorem providing (7.1) and (7.2), or the weaker E_m^X=o(1) plus a strict F-only gap.
- No finite evidence promoted to a cofinal quantifier. No new spectral positivity or eigenvector-selection result claimed.

Predictions were registered in a local record before executing Appendix A: P1 exact even compression CONFIRMED; P2 finite-data coverage limitation CONFIRMED by source; P3 absolute-to-relative shortcut REFUTED by exact plant; P4 polynomial high-energy removal established algebraically using inherited residual/envelope. The code does not verify those inherited analytic suppliers. Seven exact groups passed. No independent analyst, Lean, Arb or new literal matrix scan was used.

## Appendix A. Executed exact checks and rounded-data arithmetic

The code below is byte-identical to the standalone checks file at delivery. Its controls are not substituted for the analytic proofs or the missing cofinal source bounds.

```python
#!/usr/bin/env python3
"""Exact algebra for the NOESCAPE F-only attempt; no RH or interval certificate.

Run from the directory containing this file:
  uv run --with sympy PROSHKA_NOESCAPE_F_ONLY_CHECKS_2026-11-02.py

The optional --output value is the JSON file created by this script.
Displayed m16 numbers are rounded source data, NOT error enclosures.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from pathlib import Path


def checks() -> dict:
    import sympy as s
    x, L = s.symbols('x L', real=True, positive=True)
    def raw(i: int, j: int):
        assert i != j
        return (s.sin(2*s.pi*j*x)-s.sin(2*s.pi*i*x))/(s.pi*(i-j))
    for n in range(2,9):
        for j in range(n):
            dj = 1 if j == 0 else s.sqrt(2)
            compressed = s.sqrt(2)*raw(n,0) if j==0 else raw(n,j)+raw(n,-j)
            target = s.sqrt(2)*dj*(j*s.sin(2*s.pi*j*x)-n*s.sin(2*s.pi*n*x))/(s.pi*(n*n-j*j))
            assert s.simplify(compressed-target)==0
    print('PASS even high-low correlation including j=0')

    def pole(i: int,j: int):
        return 32*L*s.sinh(L/4)**2*(L**2-16*s.pi**2*i*j)/((L**2+16*s.pi**2*i*i)*(L**2+16*s.pi**2*j*j))
    def u(j: int):
        dj = 1 if j==0 else s.sqrt(2)
        return 4*s.sqrt(2)*dj*L**s.Rational(3,2)*s.sinh(L/4)/(L**2+16*s.pi**2*j*j)
    for n in range(2,7):
        for j in range(n):
            compressed=s.sqrt(2)*pole(n,0) if j==0 else pole(n,j)+pole(n,-j)
            assert s.simplify(compressed-u(n)*u(j))==0
    print('PASS literal pole even compression')

    z=s.symbols('z', positive=True)
    pol=16*z*z-24*z
    for k in range(4):
        expr=s.exp(x/2)*pol.subs(z,s.exp(2*x))*s.exp(-s.exp(2*x))
        nxt=s.expand(pol/2+2*z*(s.diff(pol,z)-pol))
        expected=s.exp(x/2)*nxt.subs(z,s.exp(2*x))*s.exp(-s.exp(2*x))
        assert s.simplify(s.diff(expr,x)-expected)==0
        pol=nxt
    print('PASS theta derivative-polynomial recurrence')

    n,j,Bn,Bj=s.symbols('n j Bn Bj',real=True)
    assert s.simplify((n+j)/(n*n-j*j)-1/(n-j))==0
    t,k=s.symbols('t k',positive=True)
    assert s.simplify(s.diff(t**(-k-1)/(k+1),t)+t**(-k-2))==0
    assert s.simplify(s.diff(t**(-k)/k,t)+t**(-k-1))==0
    print('PASS row-envelope cancellation and exact tail antiderivatives')

    # Abstract controls: neither is claimed to be a CCM source.
    for eps in (F(1,4),F(1,16),F(1,256)):
        lam=eps
        fb=eps*eps
        xb=-eps-eps*eps
        assert fb+xb == -lam
        assert (fb/lam)**2 == eps**2
        assert abs(xb)<=2*eps
        assert abs(xb/fb)==1/eps+1
        assert ((fb+xb)/lam)**2==1
    print('PASS tiny absolute exterior + tiny F-only mass can hide total excited mass one')

    for eps in (F(1,4),F(1,16),F(1,256)):
        lam=eps-eps**3
        fb=-eps
        xb=eps**3
        assert fb+xb==-lam
        assert abs(xb/fb)==eps**2
        assert (fb/lam)**2==1/(1-eps**2)**2 > 1
    print('PASS relative exterior smallness alone gives no strict c<1')

    data={
       '1': dict(lam='4.73342e-32', F='4.2273939e-33', X='-4.00561e-37', D='9.47626e-5'),
       '2': dict(lam='7.34649e-27', F='-3.2021385e-29', X='-5.00248e-34', D='1.56221e-5'),
       '3': dict(lam='4.62977e-22', F='1.1376201e-25', X='-3.68657e-31', D='3.24061e-6')}
    Z=F('2.26186405237')
    subtotal=F(0); rows=[]
    for i,row in data.items():
        lam,ff,xx,dd=(F(row[k]) for k in ('lam','F','X','D'))
        mass=(ff/(Z*lam))**2
        subtotal+=mass
        rows.append(dict(i=int(i),F_only_mass=float(mass),abs_X_over_F=float(abs(xx/ff)),D_over_one_minus_D=float(dd/(1-dd))))
    print('PASS rounded-data arithmetic; only indices 1,2,3, not full m16 sum')
    return dict(status='EXACT_ALGEBRA_AND_ROUNDED_DATA_AUDIT_NOT_A_CERTIFICATE',
                exact_groups=7, m16_rounded_data_rows=rows,
                m16_first_three_excited_F_subtotal=float(subtotal),
                full_m16_sum_computed=False,
                independent_X_computed=False,
                cofinal_bounds_proved=False)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=None,
                        help='optional JSON output, e.g. noescape_f_only_checks.json')
    args=parser.parse_args()
    data=checks()
    text=json.dumps(data,indent=2)
    print(text)
    if args.output is not None:
        args.output.write_text(text+'\n',encoding='utf-8')

if __name__=='__main__':
    main()
```

Code SHA-256: `6d10180ad66308b81bb7dd8bc97f4ee1bf1f91f04e002512cd08cc26dd9fbf28`.
