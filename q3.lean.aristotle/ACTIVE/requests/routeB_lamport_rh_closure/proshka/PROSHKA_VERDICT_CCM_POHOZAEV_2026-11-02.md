# STATUS: RUN_CCM_POHOZAEV_BOUNDARY_LIMIT_REPAIR
```yaml
OPERATIVE_CLASS: RUN_CCM_POHOZAEV_BOUNDARY_LIMIT_REPAIR
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_REQUEST_FOR_FULL_CCM_POHOZAEV_IDENTITY
SOURCE_REPOSITORY: Malaeu/chen_q3
SOURCE_COMMIT: da3459f48c2823e99e6f1376c237c75906bf12c6
SOURCE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_CCM_INFINITE_WINDOW_2026-11-02.md
SOURCE_SHA256: 91e1928f76d192083263cc6d83a8e2bcafbd5a23881ac37a69f4050b1f63b600
SOURCE_GIT_BLOB: e8bd22411090230102b353c7c22ea25c314dde51
SOURCE_BYTES: 47664
SOURCE_LF_LINES: 566
SOURCE_HASH_CHECK: MATCH
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
REQUESTED_POHOZAEV_IDENTITY_PROVED: false
REQUESTED_GAMMA_DETERMINED: false
CITED_ARXIV_2411_15985: WITHDRAWN_2025_04_26_FOR_CRUCIAL_ERROR_IN_POHOZAEV_PROOF
THM_2_3_REQUIRES_NORMALIZED_BOUNDARY_LIMIT_AS_HYPOTHESIS: true
SMALL_ORDER_BOUNDARY_LIMIT_INTERCHANGE: GENERIC_THEOREM_SHAPE_REFUTED
FORM_CONVERGENCE_PRESERVES_NORMALIZED_TRACE: GENERIC_THEOREM_SHAPE_REFUTED
FULL_REGULAR_DILATION_PART_WITHOUT_W11: PROVED_PAPER
EXACT_ATOMIC_FINITE_DIFFERENCES: RETAINED
FRACTIONAL_REGULARIZATION_BOTTOM_CONVERGENCE: PROVED_PAPER_USING_PINNED_FORM_REALIZATION
FRACTIONAL_BOUNDARY_FLUX_CONVERGENCE: NOT_PROVED
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: SOURCE_EXACT_REGULAR_VARIATION_AND_BULK_APPROXIMATION
KILL_SCOPE: THEOREM_SHAPE
FAILURE_TYPE: COUNTEREXAMPLE_AND_INVALID_IMPORT
COGNITIVE_OPERATOR: BOUNDARY_CASE
ROUTE_SCORE: 4
VERIFIER: PAPER
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_ASSUMED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Вердикт

Требуемое равенство с классическим нормированным граничным пределом и определённым коэффициентом Gamma в этом батче **не доказано**. Причина не в том, что цель связана с RH, а в конкретном неподтверждённом предельном переходе. Названный внешний поставщик отозван именно из-за ошибки в доказательстве тождества Похожаева.

Уже в формулировке Theorem 2.3 v1 существование предела `u(x)^2 log(d(x)^(-2))` является предпосылкой. Закреплённый CCM-вердикт даёт только его ограниченность и отдельно оставляет существование предела открытым. Схема из статьи не закрывает эту предпосылку.

Ниже: точный источник отзыва; явный контроль перестановки двух пределов; отказ от ложного переноса следа через плотность; исходниковая вариация всей регулярной части без W^{1,1}; точный остаток от атомов; корректная дробная аппроксимация нижнего уровня. Это не опровержение возможности настоящего CCM-тождества Похожаева.

## 1. Source lock и проверенные внешние сведения

**[ABSTRACT | PAPER: provenance.]** Локальные байты S1 пересчитаны: 47664 bytes, 566 LF, SHA-256 и Git blob совпадают с header. GitHub connector вернул тот же blob в указанном коммите. S1 прочитан полностью. Его внутренние номера, относящиеся к запросу: (4.6)–(4.9), §5 и (7.1-new). Нумерация краткой чат-сводки не подменяет внутреннюю нумерацию файла.

S1 — `PROSHKA_VERDICT_CCM_INFINITE_WINDOW_2026-11-02.md`, pin выше. Наследуются его закрытая форма, достижение минимума, компактность, ограниченность и логарифмическая краевая оценка. Нового независимого аудита этих утверждений не заявляется.

E1 — R. Arora, J. Giacomoni, A. Vaishnavi, arXiv:2411.15985v1 (24 Nov 2024), Theorem 2.3, p.7; proof §3.2, pp.17–19. Страница arXiv и v2 (26 Apr 2025) сообщают об отзыве из-за существенной ошибки в доказательстве Pohozaev identity. Именно v1 содержит запрошенный Theorem 2.3. **E1 не импортируется как теорема.**

E2 — те же авторы, arXiv:2504.18907v3 (17 Sep 2025), Introduction (1.1), (1.2), (2.1) и §6. Прочитаны названные места: они не поставляют требуемый CCM boundary-flux theorem. Это не заявление об отсутствии всех возможных результатов в литературе.

E3 — Hernández-Santamaría–López Ríos–Saldaña, DCDS 45 (2025), arXiv:2401.18033, используется только в том объёме, в котором S1 уже вывел краевую верхнюю оценку. Новый нормированный след из E3 не импортируется.

PDF E1 доступен в разобранном тексте; вызовы web-screenshot для pp.7,17–19 вернули Cache miss. Дополнительная загрузка в контейнер не удалась. Поэтому визуальная проверка PDF не заявляется; математические фрагменты сверены в извлечённом тексте. rStation Paper 67 обнаружен поиском, но полный текст недоступен и не использован как поставщик.

## 2. Почему указанный импорт не даёт результата

**[ABSTRACT | PAPER: audit of the stated hypotheses.]** В E1, Theorem 2.3, помимо ограниченного слабого решения, предполагаются:

- существование и интегрируемость нормированного граничного предела;
- ограниченность L_Delta u;
- локальное представление правой части F(x,u) с Lipschitz-регулярностью по x.

S1 обеспечивает вторую предпосылку. Первая отсутствует. Для третьей полный CCM имеет не локальную заданную нелинейность, а
\[
L_\Delta f=2\left[(\lambda+c_*)f+
\sum_{a_n<L}\omega_n(T_{a_n}f+T_{-a_n}f)
-\langle p,f\rangle p-\mathcal R_Lf\right].
\tag{2.1}
\]
Ограниченность этой правой части не равна её Lipschitz-регулярности. Заморозить неизвестный f внутри сдвигов и назвать результат F(x,t) можно как запись, но это не доказывает нужное свойство F. Делить на f тоже нельзя: возможные нули не исключены.

Кроме того, S1 даёт производную нижнего уровня лишь почти всюду. В каждой заранее заданной точке дифференцируемость и простота не установлены. Это независимое ограничение точечной записи L lambda'(L).

### 2.1. Точный контроль перестановки s -> 0 и d -> 0

**[ABSTRACT | PAPER; boundary-profile control, not a CCM eigenfunction.]** Пусть
\[
u(d)=\frac1{\sqrt{\log(1/d)}},\qquad 0<d<e^{-2}.
\]
Тогда u(d) -> 0 и
\[
u(d)^2\log(d^{-2})=2.
\]
Рассмотрим ровно разность, возникающую в малопорядковом расширении дробного граничного множителя:
\[
R(s,d)=\frac{u(d)^2}{2s}(d^{-2s}-1)
=\frac{e^{2s\ell}-1}{2s\ell},\qquad \ell=\log(1/d).
\tag{2.2}
\]
При фиксированном d предел s -> 0 равен 1. При фиксированном s > 0 предел d -> 0 равен +infinity. Поэтому
\[
\boxed{\lim_{d\downarrow0}\lim_{s\downarrow0}R(s,d)=1,
\qquad\lim_{s\downarrow0}\lim_{d\downarrow0}R(s,d)=+\infty.}
\tag{2.3}
\]
Это элементарный строгий контроль именно перестановки на p.18 E1 перед (3.11), а не утверждение, что данный профиль является решением CCM. Существование логарифмического следа даже само по себе не делает эту перестановку законной. Фиксированный профиль с логарифмическим затуханием вообще не имеет конечного дробного следа u/d^s при s > 0.

Для гладкого фиксированного теста Taylor-разложение по s законно в подходящих внутренних нормах. Это другое утверждение. При d -> 0 малая величина для Taylor-контроля — s log(1/d), а не одно s.

### 2.2. Форменное приближение не переносит нормированный след

**[ABSTRACT | PAPER; controls inside the literal form domain, not eigenfunctions.]** На каждом конце фиксированного окна зададим предыдущий профиль с гладким сопряжением внутри. Получим чётный ограниченный BV-профиль u с нулевым обычным следом и нормированным квадратом следа 2.

Пусть u_delta совпадает с u при расстоянии от границы >= 2delta и равен нулю при расстоянии <= delta, с гладким переходом. Тогда u_delta имеет компактную поддержку внутри окна и нормированный след 0. Однако
\[
\|u-u_\delta\|_2^2+\mathcal A[u-u_\delta]=O_L(\delta)\longrightarrow0.
\tag{2.4}
\]
**Доказательство бюджета.** Для v_delta=u-u_delta поддержка имеет длину O(delta),
\[
\|v_\delta\|_\infty=O(\ell_\delta^{-1/2}),\quad
\operatorname{TV}(v_\delta)=O(\ell_\delta^{-1/2}),\quad
\|v_\delta\|_2^2=O(\delta/\ell_\delta),\quad
\ell_\delta=\log(1/\delta).
\]
BV-оценка сдвига и тривиальная L2-оценка дают
\[
\|v_\delta-T_sv_\delta\|_2^2
\le C\min(s,\delta)/\ell_\delta.
\]
Интегрирование против j(s) <= C/s на (0,1) и его интегрируемого хвоста даёт (2.4). Конечные prime- и pole-операторы ограничены в L2 и тоже не препятствуют сходимости. Дополнительная внутренняя моллификация сохраняет нулевой след и приближение. ∎

Таким образом, плотность гладких компактных тестов не позволяет восстановить ненулевой нормированный след. Именно такой новый контроль нужен для аппроксимационного шага E1; форменная плотность его не заменяет.

Ещё более простая граница: профиль
\[
\frac{2+\sin(\log\log(1/d))}{\sqrt{\log(1/d)}}
\tag{2.5}
\]
также ограничен, непрерывен с нулевым следом, локально BV и удовлетворяет краевой верхней оценке S1, но его нормированный квадрат не имеет предела. Он не заявляется eigenfunction или решением с bounded forcing. Он отделяет верхнюю оценку от существования предела.

## 3. Полная дилатация без W^{1,1}: регулярная часть закрывается

**[ABSTRACT | PAPER; literal full form.]** Пусть f — любой вещественный чётный единичный элемент D_L^E, продолженный нулём. Для tau в окрестности нуля положим
\[
(U_\tau f)(x)=e^{-\tau/2}f(e^{-\tau}x),\qquad
\operatorname{supp}U_\tau f\subset I_{Le^\tau}.
\]
Норма и чётность сохраняются. Обозначим
\[
Q_f(s)=2\int f(x)f(x+s)dx,\quad
m_j(s)=(sj(s))',\quad
p(x)=\sqrt2\cosh(x/2),\quad q(x)=\sqrt2\sinh(x/2),
\]
\[
A_f=\langle p,f\rangle,\qquad B_f=\langle xq,f\rangle.
\]
Q_f непрерывна, |Q_f| <= 2 и Q_f(s)=0 при s >= L. Никакая производная f не нужна.

### 3.1. Архимедов член

Точно
\[
\mathcal A[U_\tau f]
=e^\tau\int_0^\infty j(e^\tau s)[2-Q_f(s)]ds.
\tag{3.1}
\]
При s -> 0:
\[
j(s)=\frac1{2s}+\frac14+O(s),\qquad m_j(s)=\frac14+O(s).
\]
На бесконечности m_j экспоненциально убывает. Поэтому m_j принадлежит L1 и
\[
\int_0^\infty m_j(s)ds=[sj(s)]_0^\infty=-\frac12.
\]
Дифференцирование (3.1) после вычитания сингулярной части обосновано L1-доминированием и даёт
\[
\boxed{\left.\partial_\tau\mathcal A[U_\tau f]\right|_0
=-1-\int_0^\infty m_j(s)Q_f(s)ds.}
\tag{3.2}
\]
Это весь arch-вклад, включая бесконечный хвост. Он получен без W^{1,1}, без Q'_f и без граничного trace limit.

Имеется явный остаточный бюджет. Положим
\[
C_j=\int_0^\infty|j(s)+3sj'(s)+s^2j''(s)|ds<\infty.
\]
Сингулярные части 1/(2s) в этой комбинации сокращаются. L1-норма второй tau-производной ядра в (3.1) равна C_j после замены переменной. Отсюда
\[
\left|\frac{\mathcal A[U_\tau f]-\mathcal A[f]}\tau
+1+\int m_jQ_f\right|\le2C_j|\tau|.
\tag{3.3}
\]

Член -1 — точная нормированная дилатационная цена главного оператора (1/2)L_Delta=log|D|. Действительно,
\[
\mathcal E_0[U_\tau f]=\mathcal E_0[f]-\tau\|f\|_2^2,
\quad \mathcal E_0[f]=\frac1{2\pi}\int\log|t|\,|\widehat f(t)|^2dt.
\tag{3.4}
\]
Низкочастотный интеграл конечен, поскольку f имеет компактную поддержку и принадлежит L1. Остальная архимедова цена -int m_j Q_f не равна нулю только потому, что разность операторов ограничена. Её нельзя удалить из запрошенного тождества.

### 3.2. Полюс

После замены переменной
\[
A(\tau)=\langle p,U_\tau f\rangle
=e^{\tau/2}\int p(e^\tau x)f(x)dx,
\quad A'(0)=\frac{A_f+B_f}{2}.
\]
Следовательно,
\[
\boxed{\left.\partial_\tau |\langle p,U_\tau f\rangle|^2\right|_0
=A_f^2+A_fB_f.}
\tag{3.5}
\]
Чётная дилатация оставляет нечётный полюс равным нулю по симметрии. Скаляр -c_*||f||2^2 также не меняется.

Остаток в (3.5), делённый на tau, имеет модуль <= C_p(L,tau0)|tau| при |tau| <= tau0. Явный выбор: b=L/2, X=b exp(tau0), P_k=max_{|x|<=X}|p^{(k)}(x)|,
\[
A_0=e^{\tau_0/2}\sqrt L P_0,
\quad A_1=e^{\tau_0/2}\sqrt L(P_0/2+XP_1),
\quad A_2=e^{\tau_0/2}\sqrt L(P_0/4+2XP_1+X^2P_2),
\quad C_p=A_1^2+A_0A_2.
\tag{3.6}
\]
Это обычный Taylor-бюджет для A(tau)^2, равномерный по единичному f на данном окне.

### 3.3. Атомы остаются точными конечными разностями

Пусть a_n=log n и omega_n=Lambda(n)/sqrt(n). Определим
\[
\mathscr P_\tau[f]=-
\sum_{n\ge2}\omega_n
\frac{Q_f(a_ne^{-\tau})-Q_f(a_n)}\tau.
\tag{3.7}
\]
При |tau| <= tau0 это конечная сумма по a_n <= L exp(tau0); остальные члены точно нулевые. Все степени простых сохранены.

Соединение (3.2), (3.5), (3.7) даёт
\[
\boxed{
\frac{\mathfrak k_{Le^\tau}[U_\tau f]-\mathfrak k_L[f]}\tau
=\mathscr D_{\rm reg}[f]+\mathscr P_\tau[f]+\mathscr E_\tau[f],}
\tag{3.8}
\]
\[
\mathscr D_{\rm reg}[f]=-1-\int m_jQ_f+A_f^2+A_fB_f,
\qquad |\mathscr E_\tau[f]|\le(2C_j+C_p)|\tau|.
\tag{3.9}
\]
Это source-exact вариационный бюджет на всей области формы. Неподтверждённая производная корреляции не спрятана внутри обозначения.

Если все нужные Q'_f(a_n) существуют, (3.7) стремится к sum omega_n a_n Q'_f(a_n), то есть к старой арифметической строке. Но форменная регулярность сама по себе этого не даёт; S1 §6 уже содержит буквальный высокочастотный контроль цены такого дифференцирования.

### 3.4. Что из этого следует для самого нижнего уровня

**[ABSTRACT | PAPER; inherited attainment.]** Для любого минимизатора f при L:
\[
\lambda_0^\infty(Le^\tau)-\lambda_0^\infty(L)
\le\mathfrak k_{Le^\tau}[U_\tau f]-\mathfrak k_L[f].
\tag{3.10}
\]
В точке дифференцируемости lambda это даёт строгий guard:
\[
\boxed{
\mathscr D_{\rm reg}[f]+\limsup_{\tau\uparrow0}\mathscr P_\tau[f]
\le L\lambda_0^{\infty\,\prime}(L)
\le\mathscr D_{\rm reg}[f]+\liminf_{\tau\downarrow0}\mathscr P_\tau[f].}
\tag{3.11}
\]
Если существует общий двусторонний предел S_f в (3.7), обе стороны совпадают и
\[
L\lambda_0^{\infty\,\prime}(L)=\mathscr D_{\rm reg}[f]+S_f.
\tag{3.12}
\]
Здесь не требуется W^{1,1}; требуется конкретная корреляционная предпосылка. Она в этом батче для всех minimizers не доказана. Простота не нужна для (3.10)–(3.12) в точке, где lambda дифференцируема. В произвольной точке вместо этого остаются односторонние вариационные неравенства.

При L=a_n новый атом не мешает первому порядку: по S1 (4.8), при tau > 0 и delta=L(1-e^{-tau}),
\[
\frac{\omega_n|Q_f(a_ne^{-\tau})|}{\tau}
\le\frac{2\omega_n D_L(\lambda)^2\delta}
{\tau\log(L/\delta)}\longrightarrow0.
\tag{3.13}
\]
Это не оплачивает старые атомы и не доказывает существование нормированного endpoint limit.

## 4. Дробная аппроксимация: что удаётся провести строго

**[ABSTRACT | PAPER; fixed L, source-preserving auxiliary regularization.]** На фиксированном I_L разложим
\[
\mathfrak k_L=\mathcal E_0+\mathfrak b_L,
\]
где E0 — (3.4), а b_L — ограниченная симметричная форма на L2(I_L), включающая весь регулярный архимедов остаток, все атомы и полюс. Ограниченность следует из S1 (4.6) и конечности атомов.

Для epsilon > 0 определим
\[
\mathfrak k_{\epsilon,L}[u]=
\frac1{2\pi}\int\frac{|t|^{2\epsilon}-1}{2\epsilon}|\widehat u(t)|^2dt
+\mathfrak b_L[u],
\quad u\in H^\epsilon(\mathbb R),\quad\operatorname{supp}u\subset\overline I_L,
\tag{4.1}
\]
с сохранением чётности. Это вспомогательное семейство, не подмена целевого CCM.

Пусть lambda_epsilon(L) — его нижний уровень. Тогда
\[
\boxed{\lambda_\epsilon(L)\downarrow\lambda_0^\infty(L)
\quad(\epsilon\downarrow0).}
\tag{4.2}
\]
Из любой последовательности единичных минимизаторов можно выделить подпоследовательность, сходящуюся к полному CCM-minimizer в L2 и исходной форменной норме.

**Доказательство.** Для каждого t != 0 секущая
\[
\frac{|t|^{2\epsilon}-1}{2\epsilon}\ge\log|t|
\]
монотонно убывает к log|t| при epsilon -> 0. Отрицательная низкочастотная часть на функции с фиксированной поддержкой ограничена через ||u||2^2, поскольку |u_hat| <= sqrt(L)||u||2 и int_0^1 |log t|dt конечен. Поэтому k_epsilon >= k_L как формы, с вложением областей; положительные частоты контролируют исходную логарифмическую энергию.

Гладкие чётные функции с компактной поддержкой внутри I_L образуют core: сначала слегка сжать поддержку нормированной дилатацией, затем моллифицировать с радиусом меньше образовавшегося collar. Непрерывность дилатаций и моллификаций в логарифмической форме следует из Fourier-представления и разбиения на компакт частот и хвост. На каждом таком фиксированном гладком тесте k_epsilon -> k_L по dominated convergence. Min–max даёт (4.2).

Минимизаторы имеют ограниченную исходную форменную норму. Компактность S1 даёт L2-предел единичной нормы. Полунепрерывность и (4.2) показывают, что это минимизатор; сходимость значений k_L и ограниченной части b_L даёт сходимость архимедовых энергий и затем сильную форменную сходимость. ∎

**Чего это не доказывает.** Производная по L не обязана коммутировать с epsilon -> 0. Тем более (4.2) не даёт сходимости дробных граничных следов, делённых на epsilon. Если даже предоставить применимость дробной граничной формулы, в ней возникает величина вида
\[
\frac{\Gamma(1+\epsilon)^2}{2\epsilon}
\int_{\partial I_L}
\left(\frac{f_{\epsilon,L}}{d^\epsilon}\right)^2
(x\nu)\,dS.
\tag{4.3}
\]
Здесь дробный след берётся первым при каждом epsilon. Нужна отдельная исходниковая теорема о его пределе и его связи с
\[
\tau_\pm(f)=\lim_{d\downarrow0}f(\pm(L/2-d))^2\log(d^{-2}).
\tag{4.4}
\]
Ни (4.2), ни (2.4) этого предела не дают. Форменная сходимость совместима с потерей всего нормированного следа, как показывает §2. Нельзя получить Gamma дифференцированием одного множителя Gamma(1+epsilon)^2, игнорируя epsilon-зависимость следа.

## 5. Проверка нормировки: bulk и boundary нельзя посчитать дважды

**[ABSTRACT | PAPER; principal-model discriminator, NOT replacement CCM.]** Для чистого T=(1/2)L_Delta=log|D| дилатация даёт
\[
\lambda_j(T;L)=\lambda_j(T;1)-\log L,
\qquad L\lambda_j'(T;L)=-1.
\tag{5.1}
\]
Любая предлагаемая формула с нормированным boundary flux обязана воспроизвести именно -1. У полной формы regular arch-член в (3.9) и атомные члены не исчезают. Если boundary law впоследствии выражает всю bulk-вариацию через след, это альтернативная запись той же скорости, а не автоматическое разрешение вычесть ещё один boundary term из уже вычисленной полной производной.

Поэтому запись из запроса нуждается в точном определении её «дилатационного члена» и Gamma. В этом вердикте Gamma не угадывается, а основной оператор имеет зафиксированный коэффициент 1/2. Нулевой обычный след f(b)=0 не равен нулевому нормированному потоку и не делает (5.1) равным нулю.

## 6. Результат и один следующий проверяемый объект

**[ABSTRACT | PAPER/CONDITIONAL as explicitly separated.]** Получены: точный контртест перестановки двух пределов; контртест передачи нормированного следа форменной плотностью; полная arch/pole вариация с явным остатком без W^{1,1}; точные prime-difference quotients; корректное bulk-приближение полной CCM-формы дробными формами.

Не получены: существование tau_± для всех minimizers, предел (4.3), тождество с Gamma и классическая дифференцируемость в каждом L. Отзыв статьи не доказывает ложность самого будущего boundary law; он лишает нас названного поставщика. Контрпримеры §2 не объявлены собственными функциями буквального CCM.

Два допустимых продолжения:

| Представление | Минимальный определяющий результат | Сила / цена |
|---|---|---|
| Прямая half-line/collar нормировка | Существование (4.4) и вычисление полного support flux на eigenspaces, с атомами и полюсом | Высокая / высокая; не использует отозванный s-предел |
| Дробная eigenfunction-аппроксимация (4.1) | Равномерный двухпараметрический boundary-layer бюджет для (4.3) и его связи с (4.4) | Высокая / высокая; bulk-сходимость уже оплачена, boundary нет |

Три стыка проверены: exact dilation (регулярная часть работает); fractional monotone-form limit (bulk работает); boundary trace passage (не следует из первых двух). Vanishing identity есть для активации нового атома, а не для старых сдвигов. Collapse object — одна корректная полная boundary-flux theorem, а не дополнительная запись той же неоплаченной формулы.

**CODEX DIRECTIVE — NORMALIZED_TRACE_AND_FLUX_GATE.** На закреплённом полном CCM-источнике независимо проверить §3–4 этого вердикта и затем доказать либо опровергнуть конкретный trace/flux supplier (4.3)–(4.4), сохранив всю ограниченную часть b_L. Зафиксировать равномерный remainder, который разрешает порядок двух пределов, и guards кратности. Не использовать arXiv:2411.15985 Thm 2.3 как установленный вход. Успех: SOURCE_NORMALIZED_TRACE_FLUX_MATCH с вычисленной константой. Иначе: FIRST_UNPAID_BOUNDARY_LIMIT с точным пределом, без RH-promotion.

## 7. Consumer-first и closeout

DOWNSTREAM_CONSUMER: корректная полная вариация поддержки; RH остаётся дальнейшей целью.
ACTUAL_CONSUMER_REQUIREMENT: идентифицированный flux и контролируемая зависимость полного eigenspace от L.
ORIGINAL_REQUESTED_OBJECT: перенос E1 Thm 2.3 через малый дробный порядок.
ORIGINAL_OBJECT_IS: NOT_NECESSARY как единственный способ; доказательность E1 отозвана.
KNOWN_WEAKER_INTERFACES: (3.8)–(3.12); прямая collar-теорема вместо дробного предела.
FAILURE_TYPE: INVALID_IMPORT и COUNTEREXAMPLE для слепой перестановки/trace-density; NO_DERIVATION для настоящего boundary supplier.
EPISTEMIC_STATUS: RESEARCH_DEBT для полного CCM-тождества, MATHEMATICALLY_DEAD только для опровергнутых общих shortcuts.
KILL_SCOPE: THEOREM_SHAPE; точные свидетели (2.2)–(2.5).
REOPEN_TRIGGER: источник-специфическая равномерная оценка, контролирующая boundary layer, а не только форму.
DISCRIMINATOR: одна и та же схема должна различать нормированный след 0 у компактных приближений и след 2 у предельного профиля и воспроизводить (5.1).

Предсказания P1–P3 зарегистрированы до исполнения новых локальных тестов. P1 подтверждён точным контролем (2.3); P2 подтверждён аналитическим выводом (3.1)–(3.9); P3 подтверждён (3.13), при сохранении непокрытых старых сдвигов. Семь локальных символьных групп прошли. Это самопроверка алгебры, не независимый аудит аналитики.

Не повторять: переносить границу после s-Taylor без равномерности; выводить нормированный след из его верхней оценки; заменять nonlocal forcing локальной Lipschitz-нелинейностью без доказательства; объявлять bulk-convergence доказательством shape-derivative convergence.

## Appendix A. Исполненные проверки

Код проверяет только локальную алгебру и явные модельные пределы. Он не доказывает ни boundary regularity, ни Pohozaev identity, ни RH.

```python
#!/usr/bin/env python3
"""Exact local algebra only: no Pohozaev, eigenfunction trace or RH certificate.
Run with: uv run --with sympy checks.py
"""
import sympy as s

def main():
    x,tau,eps,ell=s.symbols('x tau eps ell',positive=True)
    j=s.exp(-x/2)/(1-s.exp(-2*x))
    m=s.diff(x*j,x)
    h=j+3*x*s.diff(j,x)+x*x*s.diff(j,x,2)
    assert s.limit(x*j,x,0,dir='+')==s.Rational(1,2)
    assert s.limit(m,x,0,dir='+')==s.Rational(1,4)
    assert s.limit(h,x,0,dir='+')==s.Rational(1,4)
    assert s.limit(x*j,x,s.oo)==0
    print('PASS 1: dilation kernels are integrable; integral m = -1/2')
    J=s.Function('J'); k=s.exp(tau)*J(s.exp(tau)*x)
    assert s.simplify(s.diff(k,tau).subs(tau,0).doit()-J(x)-x*s.diff(J(x),x))==0
    assert s.simplify(s.diff(k,tau,2).subs(tau,0).doit()-J(x)-3*x*s.diff(J(x),x)-x*x*s.diff(J(x),x,2))==0
    print('PASS 2: first and second archimedean dilation derivatives')
    p=s.sqrt(2)*s.cosh(x/2); q=s.sqrt(2)*s.sinh(x/2)
    a=s.exp(tau/2)*p.subs(x,s.exp(tau)*x)
    assert s.simplify(s.diff(a,tau).subs(tau,0)-(p+x*q)/2)==0
    print('PASS 3: exact pole derivative integrand')
    Q=s.Function('Q'); shift=s.symbols('shift',positive=True)
    assert s.simplify(s.diff(-Q(shift*s.exp(-tau)),tau).subs(tau,0)-shift*s.diff(Q(shift),shift))==0
    print('PASS 4: old-prime sign in the finite-difference quotient')
    R=(s.exp(2*eps*ell)-1)/(2*eps*ell)
    assert s.limit(R,eps,0,dir='+')==1
    assert s.limit(R,ell,s.oo)==s.oo
    assert s.simplify((1/ell)*(2*ell))==2
    print('PASS 5: boundary and small-order limits do not commute')
    N,E=s.symbols('N E',real=True)
    assert s.diff(E-tau*N,tau)==-N
    L=s.symbols('L',positive=True)
    delta=L*(1-s.exp(-tau))
    assert s.limit(delta/(tau*s.log(L/delta)),tau,0,dir='+')==0
    print('PASS 6: log multiplier dilation and o(tau) new-atom activation')
    aa,ab,bb,lam,dot=s.symbols('aa ab bb lam dot',real=True)
    # ||f||=||g||=1, g is the contracted f, ab=q(f,g)=lam*dot.
    e_r=aa+bb-2*ab; norm_r=2-2*dot
    assert s.simplify((e_r-lam*norm_r-(bb-lam)).subs({aa:lam,ab:lam*dot}))==0
    print('PASS 7: weak eigen-equation contraction identity')
    print('ALL 7 LOCAL ALGEBRA GROUPS PASSED; NO ANALYTIC TRACE CLAIM')

if __name__=='__main__':
    main()
```

Вывод: ALL 7 LOCAL ALGEBRA GROUPS PASSED; NO ANALYTIC TRACE CLAIM.

Источник E1 проверяется по arXiv:2411.15985 (withdrawal record) и отдельно arXiv:2411.15985v1, Theorem 2.3 / §3.2. Никакая внешняя статья не использована в качестве доказанного CCM boundary supplier.
