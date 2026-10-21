# STATUS: TRY_CCM_JOINT_CORRELATION_Q05
```yaml
OPERATIVE_CLASS: TRY_CCM_JOINT_CORRELATION_Q05
VERDICT_CODE: JOINT_FEJER_FOURIER_DAVENPORT_TRANSFER_PAID_NO_FULL_POWER_GAIN
DATE: 2026-10-20
REQUEST_FILE: PROSHKA_CCM_JOINT_CORRELATION_Q05_2026-10-20.txt
REQUEST_BYTES: 175378
REQUEST_LF_COUNT: 2741
REQUEST_SHA256: b893da00379ad6e45c14836686a9c7a3103590f639ac7c9b582a2090e3b95024
REQUEST_HASH_SIZE_AND_LF: MATCH
REQUEST_READ: COMPLETE_TOP_REQUEST_AND_ALL_SIX_EMBEDDED_SOURCES_INCLUDING_APPENDICES
SOURCE_HEAD_AS_SUPPLIED: 654f7fbf19b5a933f86d196b1cf9d0c3f437724b
BOOTSTRAP_REPOSITORY: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_N_EQUALS_M_ORIGINAL_THREE_CONSTRAINT_SPARSE_BAND
SCHEDULE: L=log(m), M=R=floor(m^epsilon), fixed 0<epsilon<1/32
TERMINAL_CONSUMER: SEPARATE_SPARSE_BAND_OFF_CRITICAL_WITNESS_RECEIVER
CHOSEN_MECHANISM: JOINT_SHIFT_FOURIER_AGGREGATION_AND_ACTUAL_WEIGHT_VARIATION_TRANSFER_OF_DAVENPORT
ADJUDICATION: INCONCLUSIVE_FOR_NEW_FULL_ARITHMETIC_POWER
NEW_FULL_POWER_BELOW_THREE_EIGHTHS: NOT_OBTAINED
NEW_ETA_EPSILON_TENDING_TO_ZERO: NOT_OBTAINED
NEW_COFINAL_POWER_GAIN: NOT_OBTAINED
ACTUAL_MOBIUS_ARITHMETIC_INPUT: UNCONDITIONAL_DAVENPORT_UNIFORM_LINEAR_PHASE_BOUND_FOR_EACH_FIXED_LOG_POWER
IMPORT_SCOPE: Genuine scalar Mobius prefixes; actual matrix weight transferred by a proved variation bound
NEW_AUXILIARY_SOURCE_LEMMA: "||B_m'(x)|| <= (36+14 D1+4 D2) x^(-3/2), with all disappearing cutoff terms retained"
FULL_JOINT_GRAM_BOUND: "G_m <= 18 C_a^2 a_m^2 m/(log R)^(2a) P, a_m=b_m+2(36+14 D1+4 D2)"
FULL_DIRECT_RETURN_OF_SAME_IMPORT: "||T_gtR|| <= 12 C_a a_m sqrt(m)/(log R)^a"
NEW_RETURNED_POWER: "1/2+2epsilon, up to arbitrary fixed logarithmic savings; not an improvement"
BEST_COMPLETE_CONDITIONAL_BOUND: Inherited Q03 O_epsilon(m^(3/8)*log(m)), with unchanged ZF78 premise
ZF78_USE: COMPARISON_ONLY_NOT_USED_TO_PROVE_THE_NEW_FOURIER_TRANSFER
RH_MERTENS_STRENGTH_AV_OR_TARGET_ASSUMPTION: NONE
ACTUAL_W_ALL_K_KPRIME_AND_INTERMEDIATE_P: RETAINED
FULL_SHORT_ARCH_AND_Q02_RETURNS: DISPLAYED_NO_DOUBLE_CREDIT
FIRST_INFORMATION_LOSS: Operator Abel variation majorant, then replacing actual Fourier energy by a uniform scalar-derived cap
SCOPED_OBSTRUCTION: All fixed logarithmic Fourier bounds plus amplitude and smooth variation do not imply a polynomial bound for the joint Fejer aggregate
SCOPED_OBSTRUCTION_MODEL: Explicit positive slowly decaying coefficients, NOT Mobius and NOT CCM
SCOPED_KILL_SCOPE: THEOREM_SHAPE
SCOPED_KILL_EVIDENCE_KIND: PAPER_COUNTEREXAMPLE_TO_A_RELAXED_TRANSFER_IMPLICATION
ACTUAL_ROUTE_KILL_SCOPE: NONE
FAILURE_TYPE_FOR_ACTUAL_GOAL: NO_DERIVATION
EPISTEMIC_STATUS_FOR_ACTUAL_GOAL: RESEARCH_DEBT
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROGRESS_SCOPE: Only the claimed automatic logarithmic-to-power transfer; new variation lemma is auxiliary
CONSUMER_POWER_PROGRESS: NONE
CF22_PYSR: PARKED_REOPENABLE
FULL_SP_G1_G3_RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
REPOSITORY_WRITES: NONE
LEAN_RUNS: 0
ARB_RUNS: 0
ACTUAL_CCM_SPECTRAL_RUNS: 0
INDEPENDENT_REVIEW: NOT_RUN
EXACT_LOCAL_CONTROLS: 187
EXACT_LOCAL_CONTROL_STATUS: PASS
```

Ы. **Новой полной степени в Q05 не получено.** Выполнен один корректный, количественный импорт: суммировать все сдвиговые корреляции вместе через ядро Фейера, затем использовать настоящую равномерную теорему о линейных экспоненциальных суммах Мёбиуса. В отличие от проверенного в пакете fixed-affine logarithmic Chowla, этот скалярный импорт действительно имеет нужную равномерность по Fourier-параметру. Однако его полная цена после переноса настоящего матричного веса слишком велика.

Получены: (i) явная вариационная оценка полного `B_(m,d)` с гиперболическим cutoff; (ii) полный совместный, не покомпонентный по h Fourier-return; (iii) точная локализация непроплаченной центральной Fourier-области; (iv) доказательство того, что даже все фиксированные логарифмические оценки вместе с гладкостью веса не подразумевают требуемой степенной цены. Последнее — препятствие **указанному обобщённому способу переноса**, не запрет actual cancellation.

Ни один результат ниже не улучшает принятую полную условную степень `3/8`. Называть найденную вариацию веса или дешёвую внешнюю Fourier-область новым полным арифметическим выигрышем нельзя.

## 0. Источник, границы и один выбранный ход

**[ABSTRACT | PAPER — происхождение].** Верхние строки 1–29 Q05 задают действующее поручение. Проверены байты, число LF и SHA-256 смонтированного UTF-8. Прочитан весь файл, включая шесть блоков:

1. полный Q01;
2. полный Q04;
3. ограниченная независимая приёмка Q04;
4. приёмка Q02;
5. logarithmic-correlation preflight;
6. short-window return.

Исторические «не отправлено» и старые директивы внутри приложений не заменяют текущий запрос. Протокол получен через GitHub на `rh_clean`; кроме него новое дерево репозитория не просматривалось. `SOURCE_HEAD` — pin пользователя, не новый build или аудит HEAD.

**Принятые входы:** буквальные `F,P,Q_M,K_m`; все три исходных ограничения; Q01 full-k bound и continuous identities; точная оконная сборка и её reconstruction fee; малоделительный и архимедов возвраты; Q02 `T−V`; cheap inverse Q04 только на его заявленной области. Cheap inverse в этой попытке не используется для вывода несуществующей нормы `M'`.

**Внешний арифметический вход** — Davenport estimate, формула (1.1) и частный случай Theorem 1.1 в Green–Tao, *The Möbius function is strongly orthogonal to nilsequences*, arXiv:0807.1736v4. Точные кванторы и употребление разобраны в §4. Никакой growing-shift Chowla-гипотезы нет.

**Проверяемый ход:** `полный G_D → Fourier/Fejer integral → scalar μ Fourier cancellation + actual B variation → полный G_m/T/K budget`. Обратный переход к линейной форме в §6.3 — снятие квадрата в том же импорте, не второй произвольно выбранный арифметический механизм.

До исполняемых проверок зарегистрированы Fourier/оконная идентичность, сохранение промежуточных P и mixed terms, Euler-endpoint transfer, отсутствие новой степени у полного логарифмического импорта и обнаружение намеренно испорченных шагов. Регистрация сделана **после бумажного вывода и проверки источника**, а не выдана за предсказание ещё не проведённого математического исследования. Полная запись — приложение A.

## 1. Неизменённые определения

**[FINITE_CELL | PAPER — определения источника].** Пусть `m` — целое, `L=log m>=4`, `1<=M<=m`, `2<=R<m`. В конце:
\[
 M=R=\lfloor m^\epsilon\rfloor,\qquad 0<\epsilon<1/32
 \quad\text{фиксировано до роста }m.
\]
Исходный carrier имеет `N=m`. Полоса `|j|<=M` дополняется нулями в нём; частоты остаются
\[
 \omega_j=2\pi j/L,\qquad \Omega=2\pi M/L,
 \qquad Fe_j(t)=L^{-1/2}e^{i\omega_jt}\mathbf1_{[0,L]}(t).
\]
`P` — ортогональный проектор на исходные три уравнения `b*c=v_+*c=v_-*c=0`. При фиксированном m он не меняется с d, x, Fourier-параметром или W.
\[
 Q_M(s)_{jk}=\begin{cases}
 2(1-s/L)\cos(\omega_js),&j=k,\\
 [\sin(\omega_ks)-\sin(\omega_js)]/[\pi(j-k)],&j\ne k,
 \end{cases}\quad0\le s\le L.
 \tag{1}
\]
\[
 A_m(t)=t^{-1/2}P Q_M(\log t)P,
 \qquad
 B_{m,d}=\sum_{k\le m/d}\log k\,A_m(dk),
 \qquad T=\sum_{d>R}\mu(d)B_{m,d}.
 \tag{2}
\]
Для `d>m` матрица B продолжена нулём. Все d,k — обычные целые, не идеалы CF22. Сохраняются все `dk`, в частности proper prime powers. `k=1` имеет точный вес ноль; атом `dk=m` имеет исходное `Q_M(L)=0`.

Для каждого
\[
 W=PWP\succeq0,\qquad\operatorname{Tr}W=1
 \tag{3}
\]
нужна общая верхняя граница `Tr(WT)`. При нулевом `ran P` матричные утверждения тривиальны; нормированный W тогда не вводится.

Обозначим
\[
 \mathfrak b_m=40+16\Omega,
 \quad b_{\rm small}=(56+32\Omega)\sqrt R+12(1+\log R)^2,
 \quad d_{\rm arch}=50L+8.
 \tag{4}
\]
Q01 и исходный crosswalk дают
\[
 \|B_{m,d}\|\le\mathfrak b_m/\sqrt d,
 \qquad
 PK_mP=D_m-T_{\le R}-T,
 \quad\|D_m\|\le d_{\rm arch},\quad\|T_{\le R}\|\le b_{\rm small}.
 \tag{5}
\]
Это принятые входы, не новые результаты Q05.

## 2. Все сдвиги вместе: точный Fourier-образ матричного агрегата

**[FINITE_CELL | PAPER].** Для исходного блока `I_D=(D,2D]∩Z` положим
\[
 X_d=\mu(d)B_{m,d},\qquad
 \Phi_D(\theta)=\sum_{d\in I_D}X_d e(d\theta),\qquad
 e(t)=e^{2\pi it}.
 \tag{6}
\]
Нулевая достройка при `d>m` сохраняется. Ядро Фейера нормировано как
\[
 \mathsf F_D(\theta)=\frac1D\left|\sum_{r=0}^{D-1}e(r\theta)\right|^2
 =\sum_{|h|<D}\left(1-\frac{|h|}{D}\right)e(h\theta),
 \qquad\int_{-1/2}^{1/2}\mathsf F_D=1.
 \tag{7}
\]
Точное равенство:
\[
 \boxed{G_D=\int_{-1/2}^{1/2}\mathsf F_D(\theta)
               \Phi_D(\theta)^*\Phi_D(\theta)\,d\theta.}
 \tag{8}
\]
**Доказательство.** Раскрытие произведения даёт упорядоченные `X_d X_e` с множителем `e((e-d)theta)`. Интеграл против (7) равен `1−|d−e|/D`. Это ровно Q01(23). Никакая коммутативность не нужна. ∎

В частности,
\[
 G_D=\mathcal D_D+\mathcal O_D,
 \qquad\mathcal D_D=\sum_{d\in I_D}\mu(d)^2B_{m,d}^2,
 \tag{9}
\]
а O_D содержит **все** h из запроса, с антикоммутаторами. Модуль каждого h не брался.

Для настоящего W:
\[
 \operatorname{Tr}(WG_D)=\int\mathsf F_D(\theta)
        \|\Phi_D(\theta)W^{1/2}\|_{\rm HS}^2d\theta.
 \tag{10}
\]
Здесь `HS` — сумма квадратов матричных элементов в ортонормированном базисе. Поскольку `||W^(1/2)||_HS²=Tr W=1`, оценка операторной нормы Φ даёт общую границу для (10), без платы за размерность и без перестановки адаптивного W со средним.

### 2.1. Полные k,k′ и промежуточные проекторы

Подынтегральная матрица (8) буквально равна
\[
 \sum_{d,e\in I_D}\frac{\mu(d)\mu(e)e((e-d)\theta)}{\sqrt{de}}
 \sum_{\substack{dk\le m\\e\ell\le m}}
 \frac{\log k\log\ell}{\sqrt{k\ell}}
 P Q_M(\log(dk))P Q_M(\log(e\ell))P.
 \tag{11}
\]
Совпадения `dk=eℓ`, разные произведения, `k=ℓ`, `k≠ℓ`, все prime powers и все промежуточные P находятся в (11). Гиперболические отсечения не превращены в прямоугольники. Fourier-переменная θ — вспомогательная координата индекса d, а не новая физическая частота CCM.

**Важная граница:** (8) само по себе не оценка. При θ=0 имеем ровно `Φ_D(0)=T_D`. Добавление Fourier-переменной не делает этот член автоматически осциллирующим.

## 3. Доказанный источникозависимый перенос: вариация полного B

Для применения скалярной теоремы нельзя объявить настоящий матричный вес независимым или постоянным. Его цену выводим из (1).

### 3.1. Производные ядра и граничные условия

**[FINITE_CELL | PAPER].** Положим
\[
 D_1=2/L+4\Omega,\quad D_2=4\Omega/L+4\Omega^2,
 \quad A_1=1+D_1,\quad A_2=3/2+2D_1+D_2.
 \tag{12}
\]
Тогда
\[
 \|A_m'(t)\|\le A_1t^{-3/2},\qquad
 \|A_m''(t)\|\le A_2t^{-5/2},
 \qquad A_m(m)=A_m'(m)=0.
 \tag{13}
\]
Для полноты: пусть `H_jk=1/(j-k)` вне диагонали и ноль на диагонали. Норма H не больше π: это конечное сжатие свёртки на Z, чей Fourier-множитель `sum_(n≠0)e^(inθ)/n=i(π−θ)` имеет модуль не больше π. Можно сначала использовать Abel-регуляризацию, затем предел на конечных векторах. Из (1)
\[
 Q_M(s)=\operatorname{diag}(2(1-s/L)\cos\omega_js)
 -\pi^{-1}[\operatorname{diag}(\sin\omega_js),H].
\]
Дифференцирование даёт `||Q'||<=D1`, `||Q''||<=D2`. Далее
\[
 A_m'=t^{-3/2}P(Q_M'-Q_M/2)P,
 \quad A_m''=t^{-5/2}P(Q_M''-2Q_M'+3Q_M/4)P.
\]
На `s=L` каждый элемент `Q_M'(L)` равен `−2/L`, так что
\[
 Q_M'(L)=-2\mathbf1\mathbf1^*/L,
 \qquad P\mathbf1=0.
\]
Это доказывает все части (13) с исходными частотами. Никакой дополнительный endpoint constraint не введён.

### 3.2. Реальный параметр x не изменяет источник

При фиксированном m,P определим для `1<=x<=m`
\[
 B_m(x)=\sum_{k\le m/x}\log k\,A_m(xk),\qquad
 C_m(x)=\frac1x\int_x^m\log(t/x)A_m(t)dt.
 \tag{14}
\]
На целых x это исходные B и C. За m положим `B_m(x)=0`. При пересечении `x=m/k` исчезающее слагаемое и его первая производная имеют значения
\[
 \log k\,A_m(m)=0,\qquad k\log k\,A_m'(m)=0.
\]
Следовательно, B_m — `C^1` по x, включая эти junctions; его первая производная не содержит скрытых скачков. P при этом фиксирован.

Принятые full-window identities:
\[
 \int_1^m A_m(t)dt=-H_P,\quad\|H_P\|\le4,
 \qquad\int_1^m\log t A_m(t)dt=J_P,\quad\|J_P\|\le8.
\]
Отсюда, включая нижний интеграл,
\[
 C_m(x)=\frac{J_P+\log x\,H_P}{x}
       -\frac1x\int_1^x\log(t/x)A_m(t)dt,
\]
\[
 \|C_m(x)\|\le20x^{-1/2},
 \quad \left\|\int_x^m A_m(t)dt\right\|\le4\sqrt x,
\]
\[
 C_m'(x)=-\frac{C_m(x)}x-\frac1{x^2}\int_x^m A_m(t)dt,
 \qquad\|C_m'(x)\|\le24x^{-3/2}.
 \tag{15}
\]
Это расширение ранее записанной continuous-оценки на реальный параметр; само по себе оно не новый арифметический выигрыш.

### Лемма 1. Полная производная с дискретным возвратом

**[COFINAL_FAMILY | PAPER; фактически все указанные конечные m,M,x].**
\[
 \boxed{\|B_m'(x)\|\le\mathfrak v_m x^{-3/2},
 \qquad \mathfrak v_m=36+14D_1+4D_2.}
 \tag{16}
\]

**Доказательство.** При `y=m/x` и между junctions
\[
 B_m'(x)=\sum_{k\le y}k\log k\,A_m'(xk),
 \quad C_m'(x)=\int_1^y u\log u\,A_m'(xu)du.
\]
Второе равенство следует из представления `C_m(x)=int_1^(m/x) log u A_m(xu)du`; верхняя производная границы оплачена `A_m(m)=0`.

Пусть `g_x(u)=u log u A_m'(xu)`. Тогда `g_x(1)=g_x(y)=0`, где верхний нуль использует **вторую** часть (13). Для `β(u)=floor u−u` точное суммирование Эйлера даёт
\[
 B_m'(x)-C_m'(x)=-\int_1^y\beta(u)g_x'(u)du.
\]
Атом при u=1 тоже нулевой, так как log1=0. Теперь
\[
 g_x'(u)=(1+\log u)A_m'(xu)+xu\log u\,A_m''(xu),
\]
\[
 \|g_x'(u)\|\le x^{-3/2}u^{-3/2}
       [A_1(1+\log u)+A_2\log u].
\]
Используя `|β|<=1`, `int_1^∞u^(-3/2)du=2` и `int_1^∞log u u^(-3/2)du=4`, получаем
\[
 \|B_m'-C_m'\|\le(6A_1+4A_2)x^{-3/2}
 =(12+14D_1+4D_2)x^{-3/2}.
\]
С (15) это даёт (16). По непрерывности производной оценка действует и в junctions. За m производная нулевая. ∎

**Граница результата.** Производная дискретного E здесь не выведена из его амплитуды: она посчитана отдельной quadrature-формулой с двумя правильными endpoint-нулями. Но (16) — цена вариации, а не знак суммы Мёбиуса.

В блоке получаем
\[
 \|B_m(2D)\|+\int_D^{2D}\|B_m'(x)\|dx
 \le\frac{\mathfrak a_m}{\sqrt D},\qquad
 \mathfrak a_m:=\mathfrak b_m+2\mathfrak v_m.
 \tag{17}
\]
При `2D>m` нулевая достройка сохраняет (17). В частности
\[
 \mathfrak a_m=112+16\Omega+28D_1+8D_2
 \le168(1+\Omega)^2\quad(L\ge1).
 \tag{18}
\]
На позднем исходном расписании `a_m` имеет порядок `m^(2epsilon)/L²`, а не константу. Эту плату нельзя спрятать в импорте.

## 4. Проверенный внешний арифметический вход

**[ABSTRACT | PAPER — внешняя теорема, не новая гипотеза].** Для каждого **фиксированного** `a>0` существует конечная константа `C_a>=1`, такая что
\[
 \sup_{\theta\in\mathbb R}
 \left|\sum_{n\le N}\mu(n)e(n\theta)\right|
 \le C_a\frac{N}{(\log N)^a},\qquad N\ge2.
 \tag{19}
\]
Это Davenport estimate, записанный как (1.1) у Green–Tao, arXiv:0807.1736v4, §1. Для независимой проверки количественной равномерности можно взять их Theorem 1.1 на фиксированном круге, линейный `g(n)=nθ`, и по отдельности cosine/sine Lipschitz-функции; их сложности не зависят от θ. Коэффициенты (19) — именно μ. Константа в общем случае **неэффективная**; численного значения или вычислимого старта из статьи здесь не извлечено.

В отличие от fixed-affine two-point result из пакета, (19) действительно равномерна по переменной θ. Не требуется подстановка короткого окна в теорему с растущим отношением концов. Для `D<=y<=2D`, разность двух исходных префиксов даёт
\[
 M_D(y,\theta):=\sum_{D<d\le y}\mu(d)e(d\theta),
 \qquad
 |M_D(y,\theta)|\le3C_a D/(\log D)^a.
 \tag{20}
\]
Ни growing-shift pair estimate, ни независимость знаков не импортируются. `a` может зависеть от фиксированного epsilon, но **не** выбираться как `a(m)` с потерянной константой.

## 5. Перенос (19) на настоящий матричный вес и весь агрегат

**[COFINAL_FAMILY | PAPER — при стандартной внешней теореме (19), без ZF78].** Конечное операторное суммирование Абеля даёт
\[
 \Phi_D(\theta)=M_D(2D,\theta)B_m(2D)
          -\int_D^{2D}M_D(x,\theta)B_m'(x)dx.
 \tag{21}
\]
Нулевая достройка B корректно сохраняет последний неполный d-блок. В (21) ещё есть связь настоящих коэффициентов с настоящим весом.

**Первое существенное ослабление этой попытки:**
\[
 \|\Phi_D(\theta)\|
 \le\sup_{D\le y\le2D}|M_D(y,\theta)|
       \left[\|B_m(2D)\|+\int_D^{2D}\|B_m'(x)\|dx\right].
\]
Оно не зануляет ни один член, но забывает взаимное расположение scalar-префикса и матричной производной. Из (17),(20):
\[
 \boxed{\sup_\theta\|\Phi_D(\theta)\|
 \le3C_a\mathfrak a_m\frac{\sqrt D}{(\log D)^a}.}
 \tag{22}
\]
Затем (8) и положительность F_D дают **полный** совместный результат
\[
 \boxed{G_D\preceq
 9C_a^2\mathfrak a_m^2\frac{D}{(\log D)^{2a}}P,}
 \tag{23}
\]
\[
 \boxed{\mathcal O_D\preceq
 9C_a^2\mathfrak a_m^2\frac{D}{(\log D)^{2a}}P-\mathcal D_D.}
 \tag{24}
\]
Здесь нигде не возникла `sum_h |...|`. Смешанные сдвиги действительно оценены **совместно**, но полученная общая цена всё ещё несёт почти первую степень D.

Для исходных `D_j=2^jR`, `j=0,...,J−1`, `J=ceil(log_2(m/R))`, имеем `sum D_j<2m`, `log D_j>=log R`. Следовательно,
\[
 \boxed{G_m\preceq
 18C_a^2\mathfrak a_m^2\frac{m}{(\log R)^{2a}}P.}
 \tag{25}
\]
Это оценка actual G, а не подставленная желаемая bound. Она верна, но недостаточно мала.

## 6. Полный показатель: квадрат, прямой возврат и кофинальный вариант

### 6.1. Нельзя забыть reconstruction

Принятое `T²<=2J G_m` вместе с (25) даёт
\[
 \boxed{\|T\|\le
 6C_a\mathfrak a_m\frac{\sqrt{Jm}}{(\log R)^a}.}
 \tag{26}
\]
Это одновременно ограничивает все W из (3), но усиливает цель до двусторонней нормы. Все межблочные члены оплачены J, а не объявлены нулевыми.

На исходном расписании `log R>=epsilon L/2` позднее, `J=O(L)`, `a_m=O(m^(2epsilon)/L²)`. Поэтому полный показатель (26):
\[
 \boxed{\|T\|\ll_{a,\epsilon}
     m^{1/2+2\epsilon}L^{-a-3/2}.}
 \tag{27}
\]
Он не меньше `3/8` и не стремится к нулю с epsilon. Любая фиксированная степень логарифма проигрывает разнице положительных степеней m.

### 6.2. Полная стоимость AV, включая ранг

Нельзя заменить adaptive максимум усреднением одной выбранной формы. Если использовать положительный trace, цена ранга равна
\[
 \operatorname{rank}P\le2M+1\le3m^\epsilon.
\]
Из (25), на `X<=m<2X`:
\[
 \sum_{m=X}^{2X-1}\operatorname{Tr}G_m
 \ll_{a,\epsilon}
 \frac{X^{2+5\epsilon}}{(\log X)^{2a+4}}.
 \tag{28}
\]
Та же верхняя цена доступна для `sum Tr O_m`, поскольку `O_m=G_m−D_m` с положительной диагональю. Точная отрицательная диагональная поправка сохраняется, но один её известный верхний размер не превращает (28) в меньшую положительную степень.

Бюджет AV из Q01 — `X^(1+3epsilon) log²(2X)`. Дефицит **этой вычисленной цены** имеет порядок
\[
 X^{1+2\epsilon}/(\log X)^{2a+6}.
 \tag{29}
\]
Он не убывает ни на какой неограниченной подпоследовательности при фиксированных a,epsilon. Это не нижняя граница actual G/O. Даже воображаемый бесплатный перенос веса с `a_m` заменённым на `b_m` оставил бы лишнюю степень X; такая замена не использована как факт.

### 6.3. Разрешённый откат до квадрата в том же механизме

Можно не тратить J и не оценивать G. В (22) ставим θ=0 и складываем исходные блоки. Так как `sum_j sqrt(D_j)<4sqrt(m)`, получаем
\[
 \boxed{\|T\|\le
 \mathfrak U_a(m,M,R):=
 12C_a\mathfrak a_m\frac{\sqrt m}{(\log R)^a}.}
 \tag{30}
\]
Это более дешёвый полный возврат того же импорта: цена `sqrt J` удалена. Однако он по-прежнему оценивает абсолютную величину и теряет signed межблочное сокращение.
\[
 \mathfrak U_a=O_{a,\epsilon}(m^{1/2+2\epsilon}L^{-a-2}).
 \tag{31}
\]
**Фиксированная степень осталась `1/2+2epsilon`.** Даже этот более ранний откат не даёт новой полной степени. Не предпринимается третья вариация того же scalar-majorant приёма.

## 7. Где находится масса совместного Fourier-ядра

Это проверка точной области применимости осцилляции, не объявление второй достаточной леммы доказанной.

По операторному Parseval:
\[
 \int_{-1/2}^{1/2}\Phi_D(\theta)^*\Phi_D(\theta)d\theta
 =\mathcal D_D\preceq\mathfrak b_m^2P.
 \tag{32}
\]
Для `0<|θ|<=1/2` имеем
\[
 \mathsf F_D(\theta)
 =\frac{\sin^2(\pi D\theta)}{D\sin^2(\pi\theta)}
 \le\frac1{4D\theta^2}.
 \tag{33}
\]
При `D>=4` разделим интеграл на `|θ|<D^(-1/2)` и дополнение. Тогда
\[
 0\preceq G_D^{\rm outside}\preceq\tfrac14\mathcal D_D
 \preceq\tfrac14\mathfrak b_m^2P.
 \tag{34}
\]
Для `D<4` можно взять внутреннюю область всей окружностью, внешний вклад нулевой. На всех блоках внешняя часть имеет суммарную цену не больше `J b_m²/4`; в правой части squared certificate её square-root цена — `O(J b_m)=O_epsilon(m^epsilon)`. Это вспомогательная оплата, не оценка полного T.

Однако
\[
 \int_{|\theta|\ge D^{-1/2}}\mathsf F_D(\theta)d\theta
 \le\frac1{2\sqrt D},
 \tag{35}
\]
а на центральном интервале
\[
 |\theta|\le1/(2D):\qquad
 \mathsf F_D(\theta)\ge4D/\pi^2,
 \qquad
 \int_{|\theta|\le1/(2D)}\mathsf F_D(\theta)d\theta\ge4/\pi^2.
 \tag{36}
\]
Последнее следует из `sin(pi D|θ|)>=2D|θ|`, `sin(pi|θ|)<=pi|θ|`. В θ=0 берётся устранимое значение D.

**(35)–(36) относятся к массе ядра, не к распределению actual энергии Φ.** Они не доказывают, что центральный вклад actual G велик. Но они запрещают бесплатное удаление центрального интервала только потому, что его длина мала. На нём при проходе D членов phase `e(dθ)` имеет лишь ограниченное число оборотов. В частности, θ=0 сохраняет полную actual блочную сумму.

Итак, достоинство совместной Fourier-записи — устранение суммы модулей по h. Она не превращает центральный arithmetic mean в автоматически быстрый oscillatory объект.

## 8. Доказанное препятствие указанному типу импорта

### Теорема 2. Даже все фиксированные log-bounds и гладкий вес не вынуждают новую степень

**[ABSTRACT | PAPER — только relaxed transfer class, не μ/CCM].** Существуют одна последовательность `a_n` с `|a_n|<=1` и один гладкий скалярный вес B(x), удовлетворяющие:

* для каждого фиксированного `a>0` существует `C_a` с `sup_θ |sum_(n<=N)a_n e(nθ)|<=C_a N/(log N)^a`;
* `|B(x)|<=x^(-1/2)` и `|B'(x)|<=x^(-3/2)/2`;
* диагональный бюджет `sum_(D<d<=2D)|a_dB(d)|²<=1`;

но для их полного **совместного** Fejer-агрегата
\[
 G_D\ge\frac D3\exp[-2\sqrt{\log(3+2D)}]
 \quad(D\ge2),
 \tag{37}
\]
а
\[
 T_D\ge\sqrt{D/2}\exp[-\sqrt{\log(3+2D)}].
 \tag{38}
\]
Следовательно, из перечисленных данных нельзя вывести `G_D=O(D^beta)` при фиксированном beta<1 или `T_D=O(D^eta)` при фиксированном eta<1/2.

**Доказательство.** Возьмём
\[
 a_n=\exp[-\sqrt{\log(3+n)}]>0,\qquad B(x)=x^{-1/2}.
\]
При каждом θ модуль суммы не больше суммы a_n. Разобьём её в sqrt(N). Первая часть не больше sqrt(N), вторая —
\[
 N\exp[-\sqrt{\tfrac12\log N}].
\]
Оба конверта — `O_a(N/log^a N)` для каждого фиксированного a. Тем самым выполнена **вся семья** логарифмических оценок, не только один `1/log N`.

Для `D<d<=2D`:
\[
 a_dB(d)\ge x_D:=(2D)^{-1/2}
                 \exp[-\sqrt{\log(3+2D)}].
\]
Все triangular weights и все коэффициенты в этой модели положительны. Прямая конечная сумма даёт
\[
 \sum_{i,j=1}^D\left(1-\frac{|i-j|}{D}\right)
 =\frac{2D^2+1}{3}.
 \tag{39}
\]
Поэтому `G_D>=x_D²(2D²+1)/3>=D exp(-2sqrt(log(3+2D)))/3`. Сумма D положительных членов даёт (38). Диагональ не больше `sum_(D<d<=2D)1/d<=1`.

Наконец, для любого fixed `c>0`:
\[
 D^c\exp[-2\sqrt{\log(3+2D)}]\longrightarrow\infty.
\]
Это доказывает заявленное отсутствие импликации, в том числе на любой неограниченной подпоследовательности. ∎

**Точная область.** Здесь `a_n≠μ(n)` и `B(x)≠B_m(x)` настоящей CCM. Модель не соблюдает её специальных делительных тождеств и полного ядра. Она не является actual counterexample, не опровергает Davenport и ничего не утверждает о размере настоящего T. Она опровергает только правило вывода, которое после scalarization пользуется уже исключительно (19), амплитудой, вариацией, Parseval и положительным Fejer-ядром.

Это также показывает, почему нельзя выбрать растущий logarithmic exponent a(m) без контроля C_a и получить фиктивную степень. Модель удовлетворяет всем фиксированным a одновременно, но всё равно сохраняет почти квадратнокорневой размер линейной суммы.

**KILL_SCOPE: THEOREM_SHAPE.** Указанная general transfer implication имеет точный контрпример. **Ни весь Fourier-метод, ни настоящая μ-компенсация, ни sparse CCM consumer не объявлены мёртвыми.** Дополнительная структура actual B/μ может отличать их от модели; текущая оценка (21) через sup и variation эту структуру больше не использует.

## 9. Возврат всей платы к T, V и K

Для непосредственно выведенной цены (30) имеем
\[
 T\preceq\mathfrak U_aP,
 \qquad
 PK_mP\succeq-[\mathfrak U_a+b_{\rm small}+d_{\rm arch}]P.
 \tag{40}
\]
Short-return добавлен один раз. Все его произведения `dk<=m` сохранены в исходном T_(<=R). Никакое благоприятное значение его знака не предполагается.

Если нужно именно `V=C+E_slow`, принятый Q02 даёт
\[
 T=V+\Delta_2,\quad\|\Delta_2\|\le F_2,
\]
\[
 F_2=32(1+D_1)N_D(1+2L)+\frac{\mathfrak K_2}{\pi^2m^{3/2}},
 \quad N_D=\lceil\log_2(m/R)\rceil,
 \quad\mathfrak K_2=16/3+20D_1/9+4D_2/9.
 \tag{41}
\]
Следовательно,
\[
 V\preceq(\mathfrak U_a+F_2)P.
 \tag{42}
\]
Попытка оценивает T напрямую; нет необходимости тратить ещё один F2 для обратного получения (40). Непрерывная C и slow Euler part нигде не заменялись отдельно малыми величинами.

### Сравнение с действительно лучшими прежними полными оценками

Элементарная точная μ-сборка даёт
\[
 \mathcal A_m=T_{\le R}+T,
 \qquad\|\mathcal A_m\|\le4\sqrt m L.
\]
Значит уже известно
\[
 T\preceq4\sqrt m L\,P-T_{\le R},
 \qquad PK_mP\succeq-[4\sqrt m L+d_{\rm arch}]P.
 \tag{43}
\]
Эта исходная цена при фиксированном epsilon асимптотически сильнее (30). Не выдаём импорт за улучшение даже элементарного full bound.

Лучший принятый **условный** результат остаётся Q03:
\[
 PK_mP\succeq-\mathfrak E_{3/8}P,
\]
\[
 \mathfrak E_{3/8}=2^{18}C_z\log(5+\Omega)
 [m^{3/8}+m^{1/8}(1+L)^2],
 \quad
 T\preceq\mathfrak E_{3/8}P+D_m-T_{\le R}.
 \tag{44}
\]
Здесь и только здесь сохраняется прежняя ZF78. Новое доказательство (16)–(30) её не использует и не подтверждает. При scalar T-bound у (44) добавляются `d_arch+b_small`; при exact возврате в K они сокращаются, не начисляются дважды.

| Компонента | Полная оплаченная цена | Степень при фиксированном epsilon | Статус |
|---|---|---|---|
| Q01 amplitude B_d | b_m/sqrt d | epsilon в коэффициенте | Принятый вход |
| Новая variation fee | a_m=b_m+2v_m | 2epsilon | Доказана, не cancellation |
| Joint G через Davenport | 18 C_a² a_m² m/(log R)^(2a) | 1+4epsilon | Полный valid bound, недостаточен |
| Squared T-return | 6 C_a a_m sqrt(Jm)/(log R)^a | 1/2+2epsilon | Нет нового показателя |
| Прямой θ=0 возврат | 12 C_a a_m sqrt m/(log R)^a | 1/2+2epsilon | Убирает sqrt J, не фиксированную степень |
| Внешняя Fourier-область | G_out<=J b_m²/4 | 2epsilon в squared budget, с логами | Только вспомогательный сектор |
| Short return | (56+32Omega)sqrt R+12(1+log R)² | 3epsilon/2 | Сохранён один раз |
| Arch | 50L+8 | 0 | Сохранён |
| Q02 T−V | F2 | epsilon с логарифмом | Не оценка V |
| Лучший full conditional | E_(3/8) | 3/8 при ZF78 | Не улучшен |

При fixed `a,epsilon` отношение цены (30) к `m^(3/8)L` имеет растущий степенной множитель `m^(1/8+2epsilon)`; никакой фиксированный логарифм его не оплачивает. Это сравнение **бюджетов**, не lower bound настоящего T.

## 10. Честная остановка и предыдущая развилка

**Задача Q05 не закрыта.** Не доказаны новый полный показатель ниже 3/8, `eta(epsilon)->0`, AV или новый кофинальный вывод. В попытке использован настоящий арифметический результат о μ, но после полного источникового переноса он оказался слишком слабым.

Где сохранена информация до неудачного шага:

* в (8),(10),(11) — actual matrix Fourier energy, до замены её uniform cap;
* в (21) — signed operator Stieltjes-паринг actual µ-prefix с actual B′, до sup×variation;
* ещё раньше — в исходной one-sided `Tr(WT)`, до вынужденного квадратом контроля отрицательной стороны.

Не назначаем «малость центрального Fourier-энергетического интеграла» новым готовым supplier: это по-прежнему непоставленная оценка того же источника. Нельзя продолжать простой подбор cutoff или логарифмического a в надежде получить степень. Теорема 2 объясняет, почему одних выбранных характеристик для этого недостаточно.

### Два допустимых представления при дальнейшей работе

| Представление | Что сохраняет | Решающий смысл / стоимость | Неоплаченный риск |
|---|---|---|---|
| Полный matrix Fejer integral (8), с actual weight внутри интеграла | Все h,k,k′ и P; адаптивность W | Высокая сила проверки source mapping; низкая алгебраическая стоимость, неизвестная высокая стоимость нового арифметического bound | Scalar cap опять стирает source coupling; квадрат сильнее цели |
| Прямая one-sided (2), либо `2 Re<f,M'_half Z_half f>` с cheap inverse Q04 | Межблочный знак и только нужную верхнюю сторону | Высокая сила против потери отрицательного кредита; формула уже известна, нового тяжёлого расчёта не требует | Отдельные нормы возвращают прежнюю half-power цену |

Это не две новые гипотезы и не разрешение на очередной широкий эксперимент. Открытый математический долг не переименован в выполненный результат.

## 11. Проверки, дискриминаторы и их область

**[FINITE_CELL | PAPER — точные локальные контроли].** Выполнены 187 тестов: matrix Fourier/window identity, полный anticommutator-return, Parseval, Cauchy reconstruction, matrix Abel с настоящими небольшими значениями μ, Euler-sign/endpoints, константы вариации, coherent-block control и степенные цены. Намеренные потери mixed terms, промежуточного P, Euler-знака и disappearing-boundary условий обнаруживаются.

Матрицы тестового стенда — рациональные некоммутирующие Hermitian-матрицы, **не** настоящие спектральные CCM. В Euler-тесте используются полиномиальные модельные функции с требуемыми граничными нулями. Они проверяют конечную алгебру и конвенции; доказательства для исходного аналитического ядра даны в §§2–3. Новых finite CCM spectral вычислений, Arb, Lean, независимого reviewer или большого scan нет. Старые 7021/620/15 проверки не пересчитаны как новая работа.

**DISCRIMINATOR основной цели.** Для заранее фиксированных `(epsilon,K,eta,m0)` проверять на законной ячейке `m>=m0` запас `K m^eta−lambda_max(T|ran P)`. Нижняя интервальная граница >=0 принимает только эту ячейку; верхняя <0 отвергает только этот контракт. При пересечении нуля нужна более высокая точность или exact свидетель, не округление. Произвольный eventual start не подгонять после данных.

**DISCRIMINATOR нового переноса.** Проверить exact (21) и (16) со всеми переходами `x=m/k`; затем Fourier identity (8) с упорядоченными B_dB_e. Только после этого разрешена цена (22). Все заявленные коэффициенты (16) и (23) должны быть возвращены без скрытого rank.

**DISCRIMINATOR нулевого центрального вклада.** Утверждение, что `G_center=0`, требует `Phi_D(theta)W^(1/2)=0` почти всюду на интервале, а для конечного полинома это тождество соответствующих коэффициентов. Малые floating-point значения или один θ=0 такого вывода не дают. В этой сессии нулевой actual central energy не заявляется.

## 12. Ledger и dependency epistemics

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| SRC | Исходные P,Q,K, Q01 full-k/short/continuous returns | COFINAL_FAMILY | PAPER | Приняты из Q05 в их границах |
| F | Matrix Fejer/Parseval (8)–(11),(32) | ABSTRACT | PAPER | Доказано; не cancellation |
| V | Literal full-k variation (16)–(18) | COFINAL_FAMILY | PAPER | Доказано с cutoff и нижней ценой |
| DA | Davenport (19) | ABSTRACT | PAPER | Внешний классический theorem, uniform θ; ineffective constants |
| TR | Actual-weight transfer (22)–(30) | COFINAL_FAMILY | PAPER | Полный bound, плохая степень |
| HF | Outer Fourier sector (34) | COFINAL_FAMILY | PAPER | Оплачен; не full T |
| NG | All log-bounds + smooth weights do not imply powers | ABSTRACT | PAPER | Точное препятствие generic inference, не actual µ |
| AV | Совместная исходная trace-average из Q01 | COFINAL_FAMILY | CONDITIONAL | Не доказана и не использована как вход |
| BEST | Q03 complete 3/8 envelope | COFINAL_FAMILY | CONDITIONAL | Прежняя ZF78, не новый результат |
| GOAL | Новый complete sparse exponent / RH | COFINAL_FAMILY | CONDITIONAL | OPEN, не предпосылка |

**DOWNSTREAM_CONSUMER:** отдельный sparse-band off-critical receiver той же полной CCM.

**ACTUAL_CONSUMER_REQUIREMENT:** one-sided upper bound полной T с `eta(epsilon)->0`, либо sufficient cofinal bound; промежуточная меньшая fixed power также была бы новым результатом.

**ORIGINAL_REQUESTED_OBJECT:** совместный агрегат actual μ-пар до модулей по h; разрешён откат до квадрата.

**ORIGINAL_OBJECT_IS:** NOT_NECESSARY как squared certificate; исходному потребителю нужна только верхняя сторона T.

**KNOWN_WEAKER_INTERFACES:** direct signed T, full prime upper bound с exact short return, joint V с оплаченной F2; none newly supplied.

**FAILURE_TYPE:** NO_DERIVATION для actual target; COUNTEREXAMPLE только для generic logarithmic-to-power inference.

**EPISTEMIC_STATUS:** RESEARCH_DEBT для actual arithmetic. **KILL_SCOPE:** THEOREM_SHAPE для утверждения, опровергнутого Теоремой 2. **PINNED_EVIDENCE:** формулы (37)–(39) и их явная глобальная модель. **ACTUAL_ROUTE_KILL_SCOPE:** NONE.

**REOPEN_TRIGGER:** источниковая оценка, использующая информацию о совместном размещении настоящих μ и B, которую scalar sup×variation удаляет, и реально уменьшающая полный показатель; не ещё один fixed log saving.

**NOVELTY_AXIS:** проверенная количественная граница одного joint Fourier-импорта; новая source variation price. Историческая новизна Fourier/Davenport метода не заявляется. Никакого доказательства невозможности настоящего сокращения или RH нет.

## 13. Одна CODEX DIRECTIVE

**Проверить один ограниченный математический пакет Q05:** (16) с genuine disappearing cutoff и `A(m)=A′(m)=0`; exact noncommutative (8),(11); uniform Davenport mapping (19)–(20); оплату `a_m` в (22); суммирование всех d-блоков, ранг в (28), прямой возврат (30) и source return (40)–(44). Отдельно проверить Теорему 2 и зафиксировать, что её коэффициенты не μ, поэтому она отвергает только generic transfer implication. Воспроизвести приложенный exact checker как конечный алгебраический контроль.

Приёмка не означает full power gain. При дефекте вернуть первый неверный шаг и исправленную цену. Не запускать новый PySR, полный CCM scan или формализацию открытой оценки. Не принимать central-arc smallness, AV, Mertens, cofinal supplier или RH как следствие принятия корректности переноса.

## 14. Closeout

**Что стало меньше:** не главный долг. Получена явная regularity-плата, позволяющая честно проверить scalar exponential-sum import на настоящем весе, и исключён неоправданный переход от всей семьи логарифмических bounds к polynomial gain.

**Что не стало меньше:** лучший полный степенной показатель. Совместный подсчёт всех h действительно избегает отдельной суммы модулей по h, но в выбранном переносе оставляет `m^(1/2+2epsilon)`.

**Что нельзя повторять:** называть удаление суммы модулей автоматическим снижением степени; забывать variation/rank; брать a=a(m) при неизвестном C_a; удалять central Fejer mass по малой длине дуги; выдавать положительную модель Теоремы 2 за источник CCM.

**Судьба прогнозов:** все зарегистрированные конечные алгебраические контроли пройдены; полный бумажный бюджет подтверждает отсутствие нового показателя. Никакого прогноза успешного закрытия original CCM не регистрировалось.

```yaml
MEMORY_ENTRY:
  iteration: CCM_JOINT_CORRELATION_Q05_2026_10_20
  target: ORIGINAL_FULL_SPARSE_CCM_ONE_SIDED_POWER
  status: OPEN
  cognitive_operator_used: LITERATURE_BRIDGE
  tested_bridge: Exact joint Fejer Fourier representation plus Davenport and actual matrix-weight variation
  paid_result: Full source-compatible transfer with explicit constants and all returns
  returned_power: 1/2+2epsilon; no improvement over inherited conditional 3/8
  first_information_loss: Supremum of scalar Mobius prefixes times total variation of B
  scoped_obstruction: All fixed logarithmic Fourier estimates and smooth weight control do not force polynomial energy decay
  actual_cancellation_impossibility: NOT_ESTABLISHED
  forbidden_future_move: Tune a logarithmic exponent or angular cutoff and claim a new full source power
  next_decisive_test: Independent paper audit of the variation and full transfer; no new open hypothesis disguised as a proved supplier
  CF22_PYSR: PARKED_REOPENABLE
  RH_fullSP_G1_G3: OPEN
```

## 15. Источники

**[S1]** Приложенный Q05 с SHA-256 из заголовка. Сырой TXT: строки 1–29 — действующий контракт; 86–1114 — полный Q01; 1117–2373 — полный Q04; 2376–2469 — Q04 conclusion; 2472–2547 — Q02 conclusion; 2550–2661 — logarithmic-correlation preflight; 2664–2741 — short-window return. Эти шесть источников прочитаны полностью. Небольшая разница завершающей пустой строки индексированной версии не меняет байты исходника.

**[S2]** Green, B.; Tao, T. *The Möbius function is strongly orthogonal to nilsequences*. arXiv:0807.1736v4, §1, formula (1.1), Theorem 1.1 и замечание об ineffective constants. Annals of Mathematics 175 (2012), 541–566. Прочитана HTML-версия; PDF не использовался. Внешняя теорема применяется только к scalar genuine μ с линейной additive phase, не непосредственно к operator weight.

```text
https://arxiv.org/html/0807.1736v4
https://annals.math.princeton.edu/2012/175-2/p03
```

Авторская сверка той же классической оценки, не отдельный поставщик новой степени:
```text
https://terrytao.wordpress.com/2021/07/05/quantitative-bounds-for-gowers-uniformity-of-the-mobius-and-von-mangoldt-functions/
```

Никакой новый предел применимости всей современной литературы не объявлен: проверен один конкретный механизм и один конкретный theorem input. Репозиторий не изменялся. PAPER-доказательства требуют независимого аудита; инструменты ниже проверяют лишь явно указанную конечную алгебру.

## Приложение A. Регистрация

```json
{
  "request": "PROSHKA_CCM_JOINT_CORRELATION_Q05_2026-10-20.txt",
  "request_sha256": "b893da00379ad6e45c14836686a9c7a3103590f639ac7c9b582a2090e3b95024",
  "mechanism": "Full noncommutative Fejer Fourier aggregate with genuine Mobius exponential sums and a proved variation return for the literal full-k matrix weight",
  "registration_boundary": "After paper derivation and source check, before the new executable algebraic tests. The elementary model and candidate constants were derived before registration and are not claimed as advance discoveries.",
  "predictions": [
    "The Laurent-coefficient Fourier integral equals the complete window Gram, with ordered intermediate-projector products retained.",
    "The exact Euler sign and both vanishing upper endpoint values are necessary for the stated C1 matrix-weight variation transfer.",
    "Davenport's uniform logarithmic bound is applicable only after paying the true weight variation; its full returned budget does not beat the inherited conditional three-eighths power.",
    "A slowly decaying positive control satisfies all fixed logarithmic Fourier bounds and a smooth weight envelope, yet its joint Fejer energy has power one; this refutes only an inference from those bounds, not actual Mobius cancellation.",
    "Deleting mixed products, a reconstruction factor, or a causal endpoint must be detected by the exact controls."
  ],
  "not_claimed": ["New full arithmetic power", "New cofinal estimate", "Actual CCM spectral certificate", "Arb", "Lean", "Independent review", "RH"]
}
```

## Приложение B. Полный локальный проверяющий

Сохранить код как `check_q05.py`, регистрацию из приложения A как `registration.json` рядом и выполнить `python3 check_q05.py`. Подстановок переменных или путей нет. Используется только стандартная библиотека; результат пишется рядом со скриптом. Это алгебраический стенд, не спектральный эксперимент CCM.

```python
"""Exact algebra controls for Q05. NOT a CCM spectral or asymptotic certificate.
Run: python3 check_q05.py. No path or parameter substitution is required.
"""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
from math import floor


def mu(n: int) -> int:
    result, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            result = -result
            if n % p == 0:
                return 0
        p += 1
    return -result if n > 1 else result


def zero(n=2):
    return tuple(tuple(Q(0) for _ in range(n)) for _ in range(n))


def add(A, B):
    return tuple(tuple(a + b for a, b in zip(ra, rb)) for ra, rb in zip(A, B))


def scale(s, A):
    return tuple(tuple(s * a for a in row) for row in A)


def product(A, B):
    n = len(A)
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(n))
                       for j in range(n)) for i in range(n))


def total(matrices, n=2):
    out = zero(n)
    for A in matrices:
        out = add(out, A)
    return out


def psd2(A):
    return (A[0][1] == A[1][0] and A[0][0] >= 0 and A[1][1] >= 0
            and A[0][0] * A[1][1] - A[0][1] ** 2 >= 0)


def polyadd(a, b):
    result = [Q(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        result[i] += x
    for i, x in enumerate(b):
        result[i] += x
    return result


def polymul(a, b):
    result = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def derivative(a):
    return [i * a[i] for i in range(1, len(a))] or [Q(0)]


def value(a, x):
    return sum(c * x ** i for i, c in enumerate(a))


def integral(a, lo, hi):
    return sum(c * (hi ** (i + 1) - lo ** (i + 1)) / Q(i + 1)
               for i, c in enumerate(a))

stats = Counter()
removed_cross_detected = False
noncommutation_seen = False
for D in range(2, 19):
    B = [((Q(i + 1, i + 3), Q((-1) ** i, i + 2)),
          (Q((-1) ** i, i + 2), Q(2 * i - 3, i + 4))) for i in range(1, D + 1)]
    X = [scale(mu(D + i + 1), B[i]) for i in range(D)]
    for i in range(D - 1):
        noncommutation_seen |= product(X[i], X[i + 1]) != product(X[i + 1], X[i])
    windows = [total(X[i - 1] for i in range(1, D + 1) if j <= i < j + D)
               for j in range(2 - D, D + 1)]
    G_window = scale(Q(1, D), total(product(C, C) for C in windows))
    # Constant Laurent coefficient of F_D(z) Phi(z)^* Phi(z).
    G_fourier = total(scale(Q(D - abs(i - j), D), product(X[i], X[j]))
                      for i in range(D) for j in range(D))
    assert G_window == G_fourier
    stats['ordered_Fejer_Fourier_window_identity'] += 1
    diagonal = total(product(C, C) for C in X)
    off = total(scale(Q(D - h, D),
                      add(product(X[i], X[i + h]), product(X[i + h], X[i])))
                for h in range(1, D) for i in range(D - h))
    assert add(diagonal, off) == G_fourier
    stats['all_shift_anticommutator_return'] += 1
    # Parseval is the zeroth coefficient of Phi^* Phi, without the Fejer weight.
    laurent = {}
    for i in range(D):
        for j in range(D):
            laurent[j - i] = add(laurent.get(j - i, zero()), product(X[i], X[j]))
    assert laurent[0] == diagonal
    stats['operator_Parseval_diagonal'] += 1
    T = total(X)
    assert psd2(add(scale(Q(2 * D - 1, D), G_fourier), scale(-1, product(T, T))))
    stats['exact_window_reconstruction_inequality'] += 1
    removed_cross_detected |= G_fourier != diagonal
    # Exact discrete Abel formula, including zero-frequency and a second phase.
    for phase in (Q(1), Q(-1)):
        a = [Q(mu(D + i + 1)) * phase ** (D + i + 1) for i in range(D)]
        prefix = []
        running = Q(0)
        for item in a:
            running += item
            prefix.append(running)
        rhs = scale(prefix[-1], B[-1])
        for i in range(D - 1):
            rhs = add(rhs, scale(-prefix[i], add(B[i + 1], scale(-1, B[i]))))
        lhs = total(scale(ai, Bi) for ai, Bi in zip(a, B))
        assert lhs == rhs
        stats['matrix_Abel_with_actual_mu'] += 1
assert noncommutation_seen and removed_cross_detected
stats['discarding_mixed_products_detected'] += 1

# Removing the intermediate projection changes the product, even for a contraction.
P = ((Q(1), Q(0), Q(0)), (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(0)))
Q0 = ((Q(0), Q(0), Q(1)), (Q(0), Q(0), Q(0)), (Q(1), Q(0), Q(0)))
compressed = product(product(P, Q0), P)
assert product(compressed, compressed) == zero(3)
assert product(product(P, product(Q0, Q0)), P) != zero(3)
stats['intermediate_projection_deletion_detected'] += 1

# Euler formula for endpoint-zero polynomials. These are test functions, not A_m.
wrong_sign_detected = False
for y in (Q(3, 2), Q(2), Q(7, 3), Q(3), Q(9, 2), Q(6)):
    for degree in range(4):
        g = polymul(polymul([Q(-1), Q(1)], [y, Q(-1)]), [Q(0)] * degree + [Q(1)])
        assert value(g, Q(1)) == value(g, y) == 0
        err = sum(value(g, Q(k)) for k in range(1, floor(y) + 1)) - integral(g, Q(1), y)
        beta_integral = Q(0)
        gp = derivative(g)
        for k in range(1, floor(y) + 1):
            hi = min(Q(k + 1), y)
            if hi > k:
                beta_integral += integral(polymul([Q(k), Q(-1)], gp), Q(k), hi)
        assert err == -beta_integral
        wrong_sign_detected |= err != beta_integral
        stats['endpoint_exact_Euler_derivative_return'] += 1
assert wrong_sign_detected
stats['wrong_Euler_sign_detected'] += 1

# A disappearing term at x=m/k has zero value AND first derivative only with both conditions.
for m in (12, 17, 31):
    for k in (2, 3, 5):
        x0 = Q(m, k)
        A = [Q(m * m), Q(-2 * m), Q(1)]
        assert value(A, k * x0) == value(derivative(A), k * x0) == 0
        assert value([Q(1)], k * x0) != 0
        assert value([Q(m), Q(-1)], k * x0) == 0
        assert k * value(derivative([Q(m), Q(-1)]), k * x0) != 0
        stats['C1_cutoff_and_planted_endpoint_failures'] += 1

# Derivative-budget arithmetic: integral u^(-3/2)=2, integral log(u)u^(-3/2)=4.
for d1 in (Q(0), Q(1, 2), Q(3), Q(10)):
    for d2 in (Q(0), Q(2), Q(7, 3)):
        quadrature = 6 * (1 + d1) + 4 * (Q(3, 2) + 2 * d1 + d2)
        assert quadrature == 12 + 14 * d1 + 4 * d2
        assert 24 + quadrature == 36 + 14 * d1 + 4 * d2
        stats['variation_constant_arithmetic'] += 1

# Exact coherent-block energy. This is a scope-limited abstract control, not Mobius.
for D in range(2, 35):
    x = Q(1, D + 1)
    G = sum(Q(D - abs(i - j), D) * x * x for i in range(D) for j in range(D))
    assert G == Q(2 * D * D + 1, 3) * x * x
    assert G >= Q(2, 3) * D * D * x * x
    stats['coherent_block_Fejer_formula'] += 1

for eps in (Q(1, 1024), Q(1, 128), Q(1, 64), Q(1, 33)):
    assert Q(1, 2) + 2 * eps > Q(3, 8)
    assert Q(3, 2) * eps < Q(3, 8)
    assert (2 + 5 * eps) - (1 + 3 * eps) == 1 + 2 * eps
    stats['complete_power_and_cofinal_deficit'] += 1

out = {
    'status': 'PASS', 'counts': dict(stats), 'total_checks': sum(stats.values()),
    'scope': 'Finite exact transfer algebra and deliberately distinct control models; not a universal CCM bound.',
    'actual_ccm_spectral_runs': 0, 'arb_runs': 0, 'lean_runs': 0,
    'independent_review': 'NOT_RUN',
    'registration_sha256': hashlib.sha256(Path(__file__).with_name('registration.json').read_bytes()).hexdigest(),
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
Path(__file__).with_name('exact_results.json').write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n')
print(json.dumps(out, ensure_ascii=False, indent=2))
```

## Приложение C. Фактический результат запуска

```json
{
  "status": "PASS",
  "counts": {
    "ordered_Fejer_Fourier_window_identity": 17,
    "all_shift_anticommutator_return": 17,
    "operator_Parseval_diagonal": 17,
    "exact_window_reconstruction_inequality": 17,
    "matrix_Abel_with_actual_mu": 34,
    "discarding_mixed_products_detected": 1,
    "intermediate_projection_deletion_detected": 1,
    "endpoint_exact_Euler_derivative_return": 24,
    "wrong_Euler_sign_detected": 1,
    "C1_cutoff_and_planted_endpoint_failures": 9,
    "variation_constant_arithmetic": 12,
    "coherent_block_Fejer_formula": 33,
    "complete_power_and_cofinal_deficit": 4
  },
  "total_checks": 187,
  "scope": "Finite exact transfer algebra and deliberately distinct control models; not a universal CCM bound.",
  "actual_ccm_spectral_runs": 0,
  "arb_runs": 0,
  "lean_runs": 0,
  "independent_review": "NOT_RUN",
  "registration_sha256": "87b97b43fae931b6fdefb30d1fef9ba8e3e26250a6c2f11e0e383176f33d803f",
  "script_sha256": "fb5629b05981289090dbac451153177b7d34b0a141364b5f4c598f786c514fa8"
}
```
