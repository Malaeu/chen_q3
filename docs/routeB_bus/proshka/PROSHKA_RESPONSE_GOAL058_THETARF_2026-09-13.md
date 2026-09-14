# STATUS: KILL_NAMED_TWOCHANNEL_RF
```yaml
OPERATIVE_CLASS: KILL_NAMED_TWOCHANNEL_RF
REQUEST_ID: REQ-2026-09-13-THETARF
RESUME_ID: REQ-2026-09-13-THETARF-RESUME
BOUNDARY_ID: GOAL058_ACTUAL_THETA_SOURCE_PROPERTY_RELATIVE_BOUND
REQUEST_COMMIT: bc02022d75f61d08bc4508372b11f43d86b67799
REQUEST_BLOB: 78b20938eb886c4033b3edd4e184ebf2d6f28dce
REQUEST_SHA256: 25f9265100eb7b2dd4e9346481abe1482750d09e1860d05f6ad3050caf28da79
RESUME_COMMIT: 78f0c8c5e8f404cb265699ad641fa3daba1c023b
RESUME_BLOB: ebdf05fb12b5f08536d4016b8427061e5b1b93b1
SOURCE_BASE: 8eacfe77fd5f70775f25715876611c36eafb94f1
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
CANDIDATE: GLOBAL_TWOCHANNEL_J_RELATIVE_DOMINATION
CANDIDATE_CHANGED: false
MECHANISM: ANALYTIC_SQUARE_ROOT_DIVISOR_OBSTRUCTION
KILL_SCOPE: THEOREM_SHAPE
KILL_EVIDENCE_KIND: FULL_SOURCE_SIMPLE_COMPLEX_DIAGONAL_ZERO_AND_REAL_NODE_JET_OBSTRUCTION
KILL_EVIDENCE_REF: "Sections 4-8; raw diagonal zero in B((237019+715864*i)/10^6,10^-5)"
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS_NAMED_RF: MATHEMATICALLY_DEAD_AT_STATED_SCOPE_PENDING_INDEPENDENT_CHECK
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
COMPUTATION: DIRECTED_DECIMAL_FULL_SOURCE_CERTIFICATE
ARB_INTERVAL: false
LEAN_VERIFIED: false
PROOF_STATE: COMPUTER_ASSISTED_PAPER_CANDIDATE_PENDING_INDEPENDENT_ACCEPTANCE
RF_PROVED: false
RF_REFUTED: true
ALL_POSITIVE_DELTA_EXCLUDED: true
ACTUAL_V_NEGATIVE_WITNESS: false
XI_ZERO_USED: false
GLOBAL_IC: OPEN_UNCHANGED
GLOBAL_ODD2: OPEN_UNCHANGED
ALL_ORDER_SOURCE_SIGN: OPEN_UNCHANGED
PX_RH_CLAIM: NOT_MADE
PRODUCTION_ADMISSION: false
SOURCE_SIGN_NO_DELTA:
  inherited: 6
  proposed_after_independent_intake: 7
  applied_to_state: false
ATTEMPTS_SINCE_LATEST_OWNER_RESUME:
  inherited_completed: 0
  this_same_THETARF_candidate: 1
PUBLICATION_BRANCH: codex_mac/math-proshka-20260912
PUBLICATION_PATH: docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_THETARF_2026-09-13.md
```

AUTOPSY: dropped=OBJECT_IDENTITY; note=The fixed diagonal-normalized carrier has a scalar feature proportional to the positive real square root of the source diagonal. A certified simple complex zero of that diagonal prevents the holomorphic extension forced by every positive all-rank RF constant. The full source V is not shown negative.

## 1. Итог: свойство источника исключает именно RF

**Ни одна положительная константа delta не удовлетворяет RF для неизменного T12/T13.** Это не вывод из открытости RH или простоты нулей. Получено другое, независимо проверяемое свойство **полного тэта-источника**: его аналитическая диагональ имеет простой невещественный нуль внутри полосы голоморфности V. Данный носитель W несовместим с этим свойством при любом положительном относительном полу.

Сохраним исходные Z=int Phi=xi(1/2), A=||Phi||_2, f=Phi/A. Для вычислений введём только положительный общий масштаб:

\[
\mathcal V=A^2V,\qquad d(z)=\mathcal V(z,z),\qquad
\mathcal W=A^2W.
\tag{1}
\]

Это не замена источника или J: V>=delta W эквивалентно calV>=delta calW с той же delta. Ни Z, ни A не вычисляются и не отождествляются.

**Доказанное свойство P_minus:**

\[
z_c=\frac{237019+715864i}{10^6},\quad \varepsilon=10^{-5};
\qquad d\text{ имеет ровно один нуль с учётом кратности в }B(z_c,\varepsilon).
\tag{2}
\]

Следовательно этот нуль прост. Это **нуль комплексного продолжения диагонали d**, не нуль xi и не реальный узел отрицательной формы. Полный сертификат даёт

\[
|d(z_c)|<\frac1{100},\quad |d'(z_c)|>9000,\quad
\sup_{|z-z_c|\le\varepsilon}|d''(z)|<10^8.
\tag{3}
\]

Запас Руше равен 3/40. Из P_minus ниже выводится невозможность всякой delta>0, а также источник-заданная последовательность конечных **реальных** строк с calW>0 и |calV|/calW->0. Знак calV на этих строках не утверждается. Все новые результаты — **PAPER-кандидаты**, до независимой проверки, не Lean/канонический приём. `[FINITE_CELL][PAPER]` `[COFINAL_FAMILY][PAPER]`

## 2. Источники, область чтения и происхождение байтов

Управляющий THETARF и RESUME прочитаны целиком непосредственно через GitHub. Original request: 13056 bytes/152 LF; его SHA256 закреплён в RESUME и указан в заголовке. Bootstrap прочитан целиком из rh_clean, blob eba04b799176c9e6a1d5f7fc4061280cfbf96ad4. Доставленный pinned URL выбирает именно эту задачу, не старые TXT других опытов.

Ниже все R/I/C/A/W/S/L относятся к SOURCE_BASE из заголовка. **Remote blob подтверждён непосредственным чтением. SHA256 и размеры R/I/C/A/L — закреплённые данные запроса, не объявляются независимо пересчитанными локально.** Для W/S локальные точные frames дополнительно извлечены из ранее доставленных TXT и заново сверены по SHA256, размеру, LF и текущему remote blob. Это не новое чтение рекурсивного архива.

| ID, путь | Bytes/LF; закреплённый SHA256 | Remote blob; реально прочитанная область |
|---|---|---|
| R `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_TWOCHANNEL_2026-09-13.md` | 56428/765; `133781768fa70c0e261de2a1f30e64dcca7d858bdaca3b98a5b8200bf1aff711` | `a450fd955683afaf7025621e55b1ef54d6cc8fe2`; весь документ, включая три приложения; старый код не перезапускался |
| I `docs/Codex/REPORT_2026-09-13_TWOCHANNEL_INTAKE.md` | 11345/233; `f8d5bd91e2c55692944af8508f272653d2dd4792dfdfba57da6366c8a5843dce` | `0e6d5c5ac9f19003708872125f46a68a5d43b62d`; весь документ |
| C `docs/Codex/REPORT_2026-09-13_TWOCHANNEL_LAPLACE_BRIDGE.md` | 11996/245; `e4e86c2ddfcee8a9146fd2dac9340a970d2fa569f09a082315262b8d2a1b8908` | `51ef75574931fde124c94a5a9df2d623460d9538`; весь документ, T1--T4 и receipts |
| A `docs/Codex/REPORT_2026-09-13_ANALYTIC_POSITIVITY_PROPAGATION.md` | 9318/178; `fb83c216aef4687425074732904f9d2f52aac77527a926e7556fb0067335e2bd` | `4c7b8bdbc362e1e65a41747c7cd6367430066974`; весь документ |
| W `docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md` | 15303/335; `1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282` | `b8b5a1a8739c946f75340f3115616d6f9ba5b40e`; §§1--2, точные объекты/Theorem T/огибающие, не повторный полный аудит транспортного доказательства |
| S `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md` | 37796/467; `14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc` | `de9578084446baecfbb2a316d7bda3da817c8c01`; BP1--BP3b, BP4--BP5, строки250--435 |
| L `docs/routeB_bus/litreview/CSORDAS_PLANAT_LOGCONCAVITY_USAGE_CARDS.md` | 4463/53; `8fa808cffa9e6e1a71e85c12808e103acf9cace85eec4c499475af377e6ffa09` | `3dc132a84024e143c545553e14c5a5503336d7d4`; весь документ |

[R]--[L] являются ссылками на указанные пути при фиксированном SOURCE_BASE. Достаточно подставить путь в `https://github.com/Malaeu/chen_q3/blob/8eacfe77fd5f70775f25715876611c36eafb94f1/{path}`. Нужные определения приведены ниже, поэтому доказательство не зависит от недоступного чата.

Внешние первичные справочные источники:

- **E1:** NIST DLMF §1.9(iii), (1.9.30)--(1.9.31), https://dlmf.nist.gov/1.9 — формула Коши и оценка производных. Непосредственно прочитаны эти формулировки.
- **E2:** NIST DLMF §1.10(iv), https://dlmf.nist.gov/1.10 — теорема Руше. Прочитана гипотеза аналитичности на/внутри контура и строгого граничного сравнения.
- **E3:** Python 3.13 Decimal, https://docs.python.org/3.13/library/decimal.html — `exp` правильно округляется ROUND_HALF_EVEN; `next_minus`, `next_plus`, контекстные операции и направленные округления. Это арифметическая зависимость сертификата, не теорема о тэта-знаке.
- **E4:** Csordas, https://arxiv.org/pdf/1309.0055 — полученная публичная копия **v2**, а не запрошенная v1, которая не открылась. Непосредственно прочитаны/отрендерены PDF/печатные страницы11--12: Theorem4.2, Remark4.3, Theorem4.6, Open Problem4.7, Remark4.8. Подтверждены различия source-кривизны, all-order эквивалентности и скалярного Laguerre-вопроса. PDF-хеш не пересчитывался. Ни v2, ни карточка Planat--Solé не используются как готовое доказательство RF.

Ни одна неназванная теорема Aronszajn/RKHS не импортируется. Рабочий «брат» — принцип: **ограниченно доминируемый скалярный признак аналитического ядра наследует его комплексную область аналитичности**. Нужная версия полностью доказана конечными разностями и E1 в §7. `[ABSTRACT][PAPER]`

## 3. Единственный механизм, регистрация и полный источник

Механизм фиксируется как **ANALYTIC_SQUARE_ROOT_DIVISOR_OBSTRUCTION**. Проверяется регулярность именно исходного сравнения, а не другой положительный носитель. До новых source-вычислений зарегистрированы P1: нечётный комплексный нуль d в полосе (p=0.60); P2: такой нуль при ненулевом канальном множителе запрещает RF (p=0.90). Буквальная регистрация и её последующее честное дополнение сохранены в Appendix D.

Контроль механизма: K(x,y)=1+xy — положительное ядро на всех реальных узлах. Но оно не доминирует никакой положительной долей u(x)u(y), u(x)=sqrt(1+x^2). На узлах -1,0,1 строка (1,-2,1) имеет K-энергию0, а u-энергию (2sqrt(2)-2)^2>0. Аналитический язык того же факта — простые нули 1+z^2 мешают целому квадратному корню. Контроль исключает ложный вывод «отказ доминирования означает отрицательность K». Это алгебра инструмента, не повтор запрещённого f_c и не новый J.

Полная функция
\[
\Phi(z)=e^{z/2}\sum_{n=1}^{\infty}P_0(\pi n^2e^{2z})e^{-\pi n^2e^{2z}},
\qquad P_0(q)=4q^2-6q
\tag{4}
\]
голоморфна в S={|Im z|<pi/4}. На любом компактном подмножестве S ряд и фиксированные производные сходятся нормально. Для z,w в компакте произведение полных рядов при z+t,w+t ограничивается C(1+t)e^{9t}exp(-c e^{2t}); это интегрируемая мажоранта. Поэтому
\[
\mathcal V(z,w)=\int_0^\infty(z+w+2t)\Phi(z+t)\Phi(w+t)dt
\tag{5}
\]
совместно голоморфна на S×S, без гипотезы о знаке. Это точный механизм [A:A2], здесь с исходной Phi, а не f.

На реальной прямой d(x)>0, d(-x)=d(x). Интегрирование полной t-производной, с исчезающим бесконечным концом, даёт
\[
d'(z)=-2z\Phi(z)^2,\quad
d(z)=d(0)-2z^2\int_0^1 s\Phi(sz)^2ds,
\quad d(0)=2\int_0^\infty t\Phi(t)^2dt.
\tag{6}
\]
Это **билинейная аналитическая диагональ** calV(z,z). Она не равна sesquilinear-величине calV(bar z,z); положительность на реальных узлах не запрещает нули (6).

Для каждого j положим
\[
P_{j+1}(q)=(1/2-2q)P_j(q)+2qP_j'(q).
\tag{7}
\]
Тогда Phi^(j) даётся (4) с P_j. Никакой нуль xi, спектральная мера или заранее положительная V не использованы. `[ABSTRACT][PAPER]`

## 4. Сертификат свойства P_minus: весь ряд и весь интеграл

### 4.1. Два интеграла с аналитическим остатком

Пусть Phi_12 — ровно первые12 слагаемых (4). Число12 является cutoff **только вычисления**, не заменой доказанного объекта. Для d(0) интегрируется 2t Phi_12(t)^2 на [0,3] с384 равными ячейками. Для второго интеграла (6) интегрируется 2z_c^2 s Phi_12(z_c s)^2 на [0,1] с128 равными ячейками.

В каждой ячейке берётся Taylor в центре до степени15. Нечётные степени интегрируются в ноль **точно**; вычисляются чётные коэффициенты0,2,...,14 из (7). На комплексном диске радиуса1/32 вокруг центра каждой ячейки ниже дан независимый верхний предел M для модуля integrand. Полуширина каждой ячейки равна1/256. Формула Коши [E1] поэтому ограничивает весь интегральный остаток через
\[
\text{длина интервала}\cdot M\frac{(1/8)^{16}}{1-1/8}.
\tag{8}
\]
Остаток не оценивается разностью двух численных квадратур.

**Реальные ячейки, комплексные окрестности.** Пусть |w-t|<=1/32, 0<=t<=3, Q=pi exp(2Re w). Тогда Q>2 и Re(pi exp(2w))>3Q/4. Положив q=Qn^2,
\[
|\Phi_{12}(w)|\le\sum_{n\ge1}(4q^3+6q^2)e^{-3q/4}<2048.
\]
Действительно q^3e^{-q/2}<=216 и q^2e^{-q/2}<=16. Оставшаяся сумма sum exp(-Qn^2/4) меньше sqrt(pi/2)<2. Поэтому верхний предел 1920<2048 достаточен. Здесь exp(Re w/2)=(Q/pi)^(1/4)<=Q, а n>=1; все члены оценены в верном направлении. Из |w|<4 следует |2w Phi_12(w)^2|<2^25.

**Наклонный отрезок.** На s-дисках |s-s_0|<=1/32, 0<=s_0<=1, w=z_c s. Используя |z_c|<19/25, получаем
\[
\Re(\pi e^{2w})>1/4,\quad |\pi e^{2w}|<7,\quad |e^{w/2}|<2.
\tag{9}
\]
Первое и второе сравнения дополнительно проверяются направленной интервальной арифметикой. Полностью аналитические суммы
\[
\sum n^4e^{-n^2/4}<128,\qquad \sum n^2e^{-n^2/4}<12
\]
дают |Phi_12(w)|<2^16. Например, для неотрицательной unimodal-функции сумма по натуральным не больше интеграла плюс её максимума: соответствующие gaussian-интегралы равны12sqrt(pi), 2sqrt(pi), а максимумы меньше16,2. Это даже сильнее выбранных констант. Следовательно |2z_c^2 s Phi_12(z_cs)^2|<2^34.

Итоговые аналитические Taylor-потери:
\[
E_0=3\cdot2^{25}\frac{(1/8)^{16}}{7/8}+10^{-90},\qquad
E_c=2^{34}\frac{(1/8)^{16}}{7/8}+10^{-25}.
\tag{10}
\]
Ниже оплачены все добавленные ошибки полного источника.

### 4.2. Все n>=13 и бесконечный реальный хвост

На действительном s-отрезке w=s z_c, 0<=s<=1,
\[
\Re(\pi e^{2w})\ge3/5,\quad |\pi e^{2w}|<6,\quad |e^{w/2}|<2.
\]
Для первой оценки log(exp(2as)cos(2bs)) вогнута, a=Re z_c, b=Im z_c; минимум находится на концах. s=0 даёт pi, а s=1 проверен направленным вычислением >3/5. Те же границы непосредственно проверены на квадрате |Re(w-z_c)|,|Im(w-z_c)|<=10^-5, содержащем круг сертификата.

При j=0,1, L_j=sum абсолютных коэффициентов P_j, имеем L_0=10, L_1=53 и
\[
|\Phi^{(j)}(w)-\Phi_{12}^{(j)}(w)|\le T_j,
\quad T_j=4L_j6^{j+2}13^{2j+4}e^{-507/5}.
\tag{11}
\]
Отношение последовательных мажорант при n>=13 ограничено
(14/13)^6 exp(-81/5)<1/2. Это оплачивает **весь бесконечный ряд**, а не только n=13. Для разности наклонных интегралов достаточно
\[
2T_0(2\cdot2^{16}+T_0)<10^{-25}.
\tag{12}
\]
Для реального t>=0 каждый отброшенный член ограничен 10q^3e^-q, q=pi n^2 exp(2t)>=3n^2. Функция q^3e^-q убывает при q>=3. Поэтому полный real-tail источника ограничен
\[
\epsilon_\theta=20\cdot3^3\cdot13^6e^{-507},\qquad
9\epsilon_\theta(4096+\epsilon_\theta)<10^{-100}.
\tag{13}
\]
Второе сравнение оплачивает разность интегралов 2t Phi² и 2t Phi_12² на [0,3].

Наконец полный источник [C:T1] даёт Phi(t)<=4pi² exp(9t/2-a), a=pi exp(2t), t>=3. Поэтому
\[
2\int_3^\infty t\Phi(t)^2dt
\le8\int_{\pi e^6}^\infty a^5e^{-2a}da<10^{-100}.
\tag{14}
\]
Здесь pi e^6>1000; при a>=1000 имеем8a^5<=e^a (достаточно десятого члена exp), так что интеграл меньше e^-1000<2^-1000<10^-100. Именно поэтому запас10^-90 в E_0 включает обе полные потери. Вторая copy исходного интеграла, центральная часть и бесконечный конец не исключены. `[ABSTRACT][PAPER]`

### 4.3. Направленная арифметика и Руше

Код Appendix A использует только Fraction и Decimal для сертификата. Реальные операции округляются наружу; exp расширяется соседними числами согласно [E3]. Sin/cos вычисляются собственной Taylor-формулой после интервального уменьшения аргумента с точной Machin-оценкой pi. Для |x|<=4 оставшийся модуль не превосходит2*4^80/80!. Ни mpmath, ни float не участвуют в доказательном запуске.

Сертификат исполнен на60 и90 знаках. Оба запуска независимо дают включения, достаточные для следующих **рациональных** выводов:
\[
|d(z_c)|<1/100,\quad |d'(z_c)|^2>9000^2,
\quad \sup_{B(z_c,\varepsilon)}|d''|<10^8.
\tag{15}
\]
Фактический upper для последнего члена меньше3.296*10^6; более слабое10^8 оставлено намеренно. d' и d'' контролируются из полного Phi и Phi' с (11):
\[
d'=-2z\Phi^2,\qquad d''=-2\Phi^2-4z\Phi\Phi'.
\]
Все literal stdout находятся в Appendix A, а не заменены округлённой таблицей.

На окружности |z-z_c|=epsilon интегральный Taylor-остаток даёт
\[
|d(z)-d'(z_c)(z-z_c)|
\le |d(z_c)|+\tfrac12\sup|d''|\varepsilon^2
<\frac1{100}+\frac1{200}=\frac3{200}.
\]
Модуль линейного сравнения больше9/100. Следовательно разность бюджетов равна
\[
\boxed{\frac9{100}-\frac1{100}-\frac1{200}=\frac3{40}>0.}
\tag{16}
\]
Обе функции голоморфны внутри/на окружности. По [E2] d имеет столько же нулей, сколько d'(z_c)(z-z_c), то есть **один с кратностью1**. Круг целиком лежит в |z|<19/25 и Im z>0. P_minus доказано. `[FINITE_CELL][PAPER]`

## 5. Канальный признак неизменного T12 и его ненулевое продолжение

Никакого нового J не вводится. В исходном обозначении [C:T12]
\[
r_x=\sqrt{x^2+4},\quad c_x=\frac{e^{x/2}}{\sqrt{2\cosh x}},\quad
B_x=\sqrt{1-1/r_x},\quad N_x^2=1+\frac1{2r_x\cosh x}.
\]
Независимая w_+-компонента sqrt(d(x))J_x равна
sqrt(d(x)) B_x c_x j_{r_x}/N_x, где
\[
j_r(s)=\sqrt2e^r e^{-e^{2r}s},\quad \|j_r\|_2=1,
\quad \langle j_r,j_0\rangle=\operatorname{sech}r.
\]
Таким образом для **каждой** конечной комплексной строки
\[
\mathcal W[c]\ge\left|\sum_i c_i u(x_i)\right|^2,
\quad u(x)=\sqrt{d(x)}a(x),\quad
 a(x)=\frac{B_x c_x}{N_x\cosh r_x}>0.
\tag{17}
\]
Это только ортогональная проекция на фиксированный единичный j_0 в уже существующем канале. Она не использует никакого знака V. Остальные три канала и межканальная связь сохраняются в положительном остатке исходной нормы [R:(11)].

Возьмём R_*=77/100. На |z|<R_* выберем ветвь r(z)=sqrt(z²+4), r(0)=2. Тогда
\[
\Re r>9/5,\quad |\Im r|<1/6,\quad
\Re\cosh z>7/10,\quad |\Im\cosh z|<2.
\tag{18}
\]
Действительно Re(z²+4)>=4-R_*²>(9/5)², а Im r=(Re z)(Im z)/Re r и |Re z Im z|<=R_*²/2. Для cosh используем cos R_*>=1-R_*²/2>7/10 и e<3.

В частности Re(r cosh z)>63/50-1/3>0; cosh r не равна нулю. Точная формула
\[
a(z)^2=
\frac{(r(z)-1)e^z}{(2r(z)\cosh z+1)\cosh^2 r(z)}
\tag{19}
\]
имеет голоморфную ненулевую правую часть на всём диске R_*. Он односвязен, поэтому она имеет единственный голоморфный квадратный корень, совпадающий с a(0)>0. Значит **a продолжается без нулей** на этот диск. Это независимый геометрический множитель носителя, не утверждение о sqrt d.

Так как d(0)>0, u имеет вещественно-аналитический germ у0. Но он не может продолжаться голоморфно на весь |z|<R_*: равенство u²=d a² и (2) дали бы нечётный порядок нуля у квадрата голоморфной функции. `[ABSTRACT][PAPER]`

## 6. Явный source-bound для всех Taylor-коэффициентов V

Следующий бюджет позволяет не прятать зависимость от порядка в абстрактной константе. На замкнутом бидиске |z|,|w|<=R_*:
\[
\boxed{|\mathcal V(z,w)|<2^{122}.}
\tag{20}
\]
Полное доказательство: для |z|<=R_*, t>=0 имеем
pi exp(2Re z)cos(2Im z)>1/100. Здесь cos(77/50)>3/100 по точной нижней Taylor-сумме до степени6; pi>3, e^-2R_*>1/9. Следовательно
\[
|\Phi(z+t)|\le5400e^{9t/2}
\sum_{n\ge1}n^4e^{-n^2e^{2t}/100}.
\]
Число5400 получается из 4pi² e^(9R_*/2)<64*81 и 6pi e^(5R_*/2)<24*9. Далее
\[
\sum n^4e^{-n^2e^{2t}/100}
\le e^{-e^{2t}/200}\sum n^4e^{-n^2/200}
\le e^{-e^{2t}/200}\,800^2\cdot20.
\]
Последняя оценка: n^4e^-n²/400<=800², а sum exp(-n²/400)<=10sqrt(pi)<20. Поэтому |Phi(z+t)|<2^37 e^(9t/2)exp(-e^(2t)/200). В (5) это даёт после u=exp(2t)
\[
|\mathcal V(z,w)|
\le 2^{74}\int_0^\infty(2R_*+2t)e^{9t}e^{-e^{2t}/100}dt
\le2^{74}\cdot2\cdot5!\cdot100^6<2^{122}.
\]
Использованы только положительные полные мажоранты. По двойной формуле Коши
\[
v_{mn}:=\frac{\partial_1^m\partial_2^n\mathcal V(0,0)}{m!n!},
\qquad |v_{mn}|\le2^{122}R_*^{-m-n}.
\tag{21}
\]
Это верно для всех порядков, без знака их матриц. `[ABSTRACT][PAPER]`

## 7. Доказательство полного отказа RF

**Лемма аналитического минорирования.** Пусть K голоморфно на бидиске радиуса R, а a_0 — аналитический germ на реальном интервале вокруг0. Если для одной delta>0
\[
\sum\overline c_iK(x_i,x_j)c_j\ge
\delta\left|\sum c_i a_0(x_i)\right|^2
\tag{22}
\]
для всех конечных комплексных строк реальных узлов около0, то a_0 продолжается голоморфно на диск радиуса R.

**Доказательство без предполагаемого RKHS.** Для каждого n фиксируем узлы jh, j=0,...,n, и реальные коэффициенты
\[
b_{j,n,h}=\frac{(-1)^{n-j}\binom nj}{n!h^n}.
\tag{23}
\]
Для достаточно малого h все они лежат в исходном интервале. Повторная основная теорема анализа в обеих переменных, затем h->0 при фиксированном n, превращает (22) в
\[
\delta\left|\frac{a_0^{(n)}(0)}{n!}\right|^2
\le\frac{\partial_1^n\partial_2^n K(0,0)}{(n!)^2}.
\]
На любом меньшем замкнутом бидиске Cauchy ограничивает правую часть через M_r r^-2n. Taylor-ряд a_0 поэтому сходится на |z|<r. Так как r<R произволен, он продолжает germ на весь диск R. Вложение H_K не было предпосылкой; положительность K потребовалась только как **следствие предполагаемого** (22). Все сопряжения сохранены. □

Предположим RF с какой-либо delta>0. Из (17) следует (22) для K=calV, a_0=u. Формулы (20)--(21) показывают непосредственно
\[
\delta|u_n|^2\le v_{nn}\le2^{122}R_*^{-2n},\qquad
u_n=u^{(n)}(0)/n!.
\tag{24}
\]
Следовательно Taylor-ряд U(z)=sum u_n z^n голоморфен на |z|<R_*. У0 он совпадает с sqrt(d)a. По тождественности
\[
U(z)^2=d(z)a(z)^2\qquad(|z|<R_*).
\tag{25}
\]
Правая часть имеет простой нуль z_* из (2), поскольку a(z_*)!=0. Слева порядок любого нуля чётен. Противоречие.

\[
\boxed{\nexists\,\delta>0:\quad V\succeq\delta W
\text{ на всех конечных реальных узлах и комплексных строках}.}
\tag{26}
\]
Это не только отказ конкретной delta и не отрицательный Ehat. Противоречие получено для **произвольной** положительной delta. Для delta>1 уже достаточно совпадающих положительных диагоналей; аргумент выше исключает и все сколь угодно малые delta. `[ABSTRACT][PAPER]`

## 8. Тот же отказ как all-rank семейство реальных строк

Для связи с буквальным тестом RF можно не останавливаться на противоречии аналитичности. Пусть u_n — коэффициенты germ u. Из (2),(19) радиус его Taylor-ряда не больше |z_*|<19/25. Поэтому существует бесконечно много n с
\[
|u_n|\ge(19/25)^{-n}.
\tag{27}
\]
Иначе ряд сходился бы хотя бы в диске19/25 и противоречил простому нулю внутри. Определим n_k как k-й индекс n>=1, удовлетворяющий (27). Это точное определение через полный источник, не sweep и не неизвестные нули xi.

Для carrier-jet
\[
w_{nn}=\partial_1^n\partial_2^n\mathcal W(0,0)/(n!)^2
\ge|u_n|^2
\]
по (17) и конечным разностям. Поэтому на выбранных индексах
\[
0\le\frac{|v_{n_kn_k}|}{w_{n_kn_k}}
\le2^{122}\left(\frac{76}{77}\right)^{2n_k}\longrightarrow0.
\tag{28}
\]
Определим h_k=2^-m_k, где m_k — наименьшее натуральное число, для которого n_k h_k<=1/k и строка (23) удовлетворяет
\[
|\mathcal V[b]-v_{n_kn_k}|\le w_{n_kn_k}/k,
\qquad
|\mathcal W[b]-w_{n_kn_k}|\le w_{n_kn_k}/2.
\tag{29}
\]
Такое число существует по гладкости полных ядер и точному пределу конечных разностей. Это существование каждого конечного шага, не численное присвоение недоказанного интервала. Оно не требует V>=0. Для полученного конкретно определённого семейства
\[
\mathcal W[b_k]>0,\qquad
\frac{|V[b_k]|}{W[b_k]}
\le2^{123}(76/77)^{2n_k}+2/k\longrightarrow0.
\tag{30}
\]
Масштаб A² сократился; все узлы jh_k реальны и лежат в[0,1/k], число узлов неограниченно. Формула (29) включает все mixed entries, а не только диагонали. Для любой delta>0 правая часть (30) в конце меньше delta/2; следовательно
\[
\boxed{\frac{(V-\delta W)[b_k]}{W[b_k]}<-\delta/2<0}
\tag{31}
\]
для всех достаточно больших выбранных k. Это требуемая **строго отрицательная верхняя огибающая** против каждой положительной delta. Никакой знак V[b_k] отдельно не выведен. Выполнение численного поиска n_k или h_k не нужно для доказательства их существования и предела, и не заявляется выполненным. `[COFINAL_FAMILY][PAPER]`

## 9. Что переносится и что остаётся открытым

**A не опровергнуто.** В [A:A3] W продолжается только на достаточно тонкую окрестность каждого реального компакта, где D не имеет нулей. Здесь доказано, что RF заставило бы отдельный канальный признак продолжаться на **более толстый диск**, доступный самому V. Сертифицированный нуль мешает именно этому. Подмены разных областей аналитичности нет.

Более того, по принятому [A] RF с одной delta на любом непустом реальном открытом интервале распространялось бы на всю R. Поэтому (26) исключает такой all-rank локальный RF на каждом интервале тоже. Ни (26), ни A не дают отрицательного V-свидетеля. Положительные региональные ODD2-результаты остаются в своей области.

Вопрос пользователя о свойстве P, которое обеспечило бы RF, разрешён отрицательно **для указанного фиксированного носителя**: никакое истинное свойство фактического Phi не может логически влечь ложное (26) при сохранённых определениях. Найденное P_minus — не переписанное RF: это независимо сертифицированное свойство одного комплексного аналитического интеграла полного источника. Теорема §7 является точным переносом P_minus **к отказу RF**, не к нужному положительному знаку.

Прежнее [R] RF=>F'^2-FF''>0=>условная простота не служит препятствием этого ответа. Ни фактический кратный нуль F, ни отрицательное Laguerre-значение не используются. Скалярная source-кривизна Csordas и его all-order словарь не изменяются. Planat--Solé не становится посылкой.

**Первый неоплаченный источник полного знака, вне уже исключённого RF:** доказать
\[
2\Re\int_0^\infty\overline{\sum_i c_i f(t+x_i)}
                \sum_j c_j(t+x_j)f(t+x_j)dt\ge0
\tag{32}
\]
для всех конечных комплексных строк, либо дать другой законно доказанный достаточный интерфейс к тому же Theorem T [W]. Формула (32) — прежний V>=0, не новая достигнутая лемма. Через принятый consumer она дала бы знак полной формы Вейля, затем RH; ни одна из этих положительных посылок здесь не доказана. `[ABSTRACT][CONDITIONAL]`

## 10. Адверсариальный аудит, K8A и независимый приём

| Возражение | Ответ и точная граница |
|---|---|
| Комплексный нуль d означает V не PSD? | Нет. d(z)=calV(z,z), не calV(bar z,z). Даже положительное K=1+xy имеет комплексные нули диагонали. |
| В RF допускаются только реальные узлы | Все строки (23),(29) реальны по узлам и коэффициентам. Комплексный анализ ограничивает их Taylor-пределы; комплексные узлы в RF не подставляются. |
| Заменён J либо выбран удобный новый carrier | Нет. (17) — проекция существующего w_+ на j_0; полная calW осталась T12/T13. |
| Код обрезает theta и t-интеграл | (11)--(14) оплачивают все n>=13 и t>=3. Taylor-потери (8)--(10) независимы от вычисленного знака. |
| Доказана только одна неудачная delta | (24)--(26) допускают любую delta>0; (31) предъявляет отрицательный relative defect для каждой. |
| Приёмка R объявляла RF открытым | Она остаётся правильным историческим состоянием. Новое P_minus там не было установлено. |
| Изучена лишь почти зависимая пара | (27)--(30) используют неограниченный порядок и ранг. Отдельная положительная пара не противоречит отказу. |
| Нужен нижний floor для W-матриц | Нет. Положительность знаменателя в (30) оплачена канальным Taylor-коэффициентом и (29), не неверным общим coefficient-floor. |
| Публикация означает независимую проверку | Нет. Результат — PAPER-кандидат; два прогона одной программы не заменяют независимого аудитора. |

K8A:

| Поле | Значение |
|---|---|
| DOWNSTREAM_CONSUMER | [W] Theorem T, затем опубликованный критерий Вейля |
| ACTUAL_CONSUMER_REQUIREMENT | Все конечные V-формы неотрицательны для всех реальных узлов и комплексных коэффициентов |
| ORIGINAL_REQUESTED_OBJECT | Одно delta>0 в RF для буквального C:T12/T13 |
| ORIGINAL_OBJECT_IS | NOT_NECESSARY как общее усиление; для настоящего источника RF теперь исключено, знак V остаётся открыт |
| KNOWN_WEAKER_INTERFACES | Непосредственное (32), либо независимый положительный decomposition с точным all-node равенством к V; каждый обязан оплатить свой полный mixed остаток |
| FAILURE_TYPE | INCOMPATIBILITY |
| EPISTEMIC_STATUS | Named RF математически исключено на PAPER-кандидатном уровне; полный source-sign UNRESOLVED |
| KILL_SCOPE | THEOREM_SHAPE, не ROUTE_FAMILY |
| NOVELTY_AXIS | Полный комплексный нуль конкретной theta-диагонали и all-rank obstruction диагонально нормированного T12; библиографическая первичность не заявляется |
| REOPEN_TRIGGER | Для named RF — выявленная ошибка сертификата/аналитического переноса; для общего V — новый независимо оплаченный source-sign вход, не технический replay |

Две репрезентации **того же отказа**, а не разрешение запустить другой J: (i) аналитический признак и нечётный divisor, §§5--7, kill-power9/10, стоимость3/10 после сертификата; (ii) реальные Taylor/конечно-разностные относительные строки §§6,8, kill-power10/10, стоимость6/10 для извлечения конкретных больших индексов. Оценки качественные, не измеренные сроки. Дальнейшее повышение рангов не нужно для настоящего вывода и не назначается.

**DISCRIMINATOR** здесь не нуль округлённого определителя: это строгий Руше-запас3/40. Для относительной формы — отрицательная верхняя оценка (31). Если независимый расчёт перестанет сертифицировать (15), маленькое floating d(z_c) само по себе не позволяет KILL.

**Одна CODEX DIRECTIVE:** независимо проверить полный сертификат §4 и конечнодifference/holomorphic minorant §7, включая ненулевой множитель (19). Сохранить все границы §9. Извлечь Appendix A без правок; выполнить `python certify_divisor.py 60` и `python certify_divisor.py 90`; проверить рациональный бюджет Appendix C; затем принять только `ACCEPT_FIXED_TWOCHANNEL_RF_DIVISOR_OBSTRUCTION` либо назвать первый неверный шаг. Не пересчитывать старые узловые/Hankel-сетки, не заменять J и не повышать V/IC/ODD2/RH. `[ABSTRACT][PAPER]`

## 11. Closeout и техническая воспроизводимость

P1 подтверждено **новым полным сертификатом**, P2 — леммой §7 и оценкой §5. Предварительные диагностические неудачи не переписаны: первый Newton ушёл к действительному хвосту; грубый contour unwrap дал недопустимый отрицательный winding и признан INVALID_AS_A_ZERO_COUNT; второй недемпфированный запуск не сошёлся; safeguarded Newton выбрал центр. Ни одно из этих значений не доказывает P_minus. Лишь затем выполнен bounded certificate (15)--(16).

Первая версия interval-кода остановилась на dispatch `I*C` с TypeError, до целевого расчёта. Исправлены две ветви Python dispatch: `I.__add__` и `I.__mul__` возвращают NotImplemented при комплексном аргументе. Не менялись математические формулы, центр или бюджеты. Полная первая версия и literal ошибка также сохранены ниже; это дефект инструмента, не отрицательный исходный сигнал. Все текущие успешные stdout действительно получены при этой сессии, а не восстановлены из утраченного TWOCHANNEL.

Никаких новых J, xi-zero вычислений, случайных матриц или Hankel-sweep не было. Были диагностические **комплексные значения одного d**, затем один полный комплексный source-сертификат с точностным повтором. Это честная граница вычислительного эксперимента, не утверждение «source evaluations=0».

**Что уменьшилось:** достаточное усиление RF исключено; оно больше не должно блокировать доказательство истинного V>=0. **Что не уменьшилось до положительного theorem:** all-order source sign. Исторический счёт6 сохраняется до независимого учёта; предлагается7 за этот единственный завершённый THETARF без source-sign поставщика. Технические RESUME/публикация не добавляют опытов. Новый опыт не запускается автоматически.

Memory: fixed diagonal-normalized positive carrier can demand analytic square roots absent from the full source diagonal; matching all real diagonals and both source-end limits does not pay all-rank relative domination. Do not substitute complex diagonal zeros for a negative physical form.

**Публикация/verification handoff:** только назначенный новый Markdown, указанная math-ветка; без изменения state/runtime/очереди/других файлов. Полный отчёт сначала сохраняется в `/mnt/data/PROSHKA_RESPONSE_GOAL058_THETARF_2026-09-13.md`. SHA публикационного коммита присваивается Contents API после этого; он сообщается отдельно, поскольку его невозможно включить в собственные неизменяемые байты без самоссылочного цикла. Родитель и однофайловый diff проверяются после записи. Lean-файлов нет; Lean-аксиомы и kernel gate не имитируются. Статус после независимой проверки может стать ACCEPTED_PAPER_AT_NAMED_RF_SCOPE; RH/canonical admission из этого не следует.

## Appendix A. Полный выполненный сертификат

Сохрани следующий блок как `certify_divisor.py`. `PREC` — число десятичных значащих цифр, `NTHETA=12` — только cutoff вычисления с доказанным полным остатком. Пример: `python certify_divisor.py 90` использует90 знаков. Команды этой сессии: `python /mnt/data/thetarf/certify_divisor.py 60` и `python /mnt/data/thetarf/certify_divisor.py 90`.

```python
"""Directed-Decimal certificate for one zero of the full theta diagonal.
No xi zeros, source node matrices, or target positivity are used.
"""
from decimal import Decimal as D, Context, getcontext, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as F
from math import factorial, comb
import sys
PREC = int(sys.argv[1]) if len(sys.argv)>1 else 60
getcontext().prec=PREC
DOWN=Context(prec=PREC,rounding=ROUND_FLOOR,Emin=-999999,Emax=999999)
UP=Context(prec=PREC,rounding=ROUND_CEILING,Emin=-999999,Emax=999999)
NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN,Emin=-999999,Emax=999999)
class I:
    __slots__=('lo','hi')
    def __init__(self,lo=0,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi;return
        if isinstance(lo,F):
            self.lo=DOWN.divide(D(lo.numerator),D(lo.denominator));self.hi=UP.divide(D(lo.numerator),D(lo.denominator));return
        self.lo=D(lo);self.hi=D(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,b):
        if hasattr(b, "im"): return NotImplemented
        b=I(b);return I(DOWN.add(self.lo,b.lo),UP.add(self.hi,b.hi))
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-I(b)
    def __rsub__(self,b):return I(b)+-self
    def __mul__(self,b):
        if hasattr(b, "im"): return NotImplemented
        b=I(b);p=[(x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(DOWN.multiply(x,y) for x,y in p),max(UP.multiply(x,y) for x,y in p))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b);assert not b.lo<=0<=b.hi
        return self*I(DOWN.divide(D(1),b.hi),UP.divide(D(1),b.lo))
    def __rtruediv__(self,b):return I(b)/self
    def __pow__(self,n):
        assert n>=0 and isinstance(n,int)
        y=I(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return max(abs(self.lo),abs(self.hi))
    def __repr__(self):return '['+str(self.lo)+', '+str(self.hi)+']'
    def widen(self,e):return self+I(-e,e)
ZERO=I(0)

def ex(a):
    a=I(a)
    return I(NEAR.next_minus(NEAR.exp(a.lo)),NEAR.next_plus(NEAR.exp(a.hi)))

def atan_recip(q,n):
    s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return (s,s+e) if n%2==0 else (s-e,s)
a,b=atan_recip(5,100);c,d=atan_recip(239,30)
PILO,PIHI=16*a-4*d,16*b-4*c
PI=I(I(PILO).lo,I(PIHI).hi)
assert PI.lo>D('3.14159') and PI.hi<D('3.14160')

def cs(a):
    a=I(a)
    mid=NEAR.divide(NEAR.add(a.lo,a.hi),D(2))
    rad=max(UP.subtract(mid,a.lo),UP.subtract(a.hi,mid))
    if rad>=1:return I(-1,1),I(-1,1)
    period=NEAR.multiply(D(2),NEAR.divide(NEAR.add(PI.lo,PI.hi),D(2)))
    k=int(NEAR.divide(mid,period).to_integral_value(rounding=ROUND_HALF_EVEN))
    x=I(mid)-2*k*PI
    assert x.ab()<D(4)
    xx=x*x;tc=I(1);ts=x;co=tc;si=ts
    # Terms through degree 79; a uniform absolute tail below 1e-65.
    for j in range(1,40):
        tc=-tc*xx/((2*j-1)*(2*j));ts=-ts*xx/((2*j)*(2*j+1))
        co=co+tc;si=si+ts
    # For |x|<=4 the remaining successive-term ratio is below 1/2.
    rem=I(F(2*4**80,factorial(80))).hi
    e=UP.add(rad,rem)
    co=co.widen(e);si=si.widen(e)
    return I(max(co.lo,D(-1)),min(co.hi,D(1))),I(max(si.lo,D(-1)),min(si.hi,D(1)))
class C:
    __slots__=('re','im')
    def __init__(self,re=0,im=0):
        if isinstance(re,C):self.re,self.im=re.re,re.im;return
        self.re=I(re);self.im=I(im)
    def __add__(self,b):b=C(b);return C(self.re+b.re,self.im+b.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,b):return self+-C(b)
    def __rsub__(self,b):return C(b)+-self
    def __mul__(self,b):
        b=C(b)
        if self.im.lo==self.im.hi==0 and b.im.lo==b.im.hi==0:return C(self.re*b.re)
        return C(self.re*b.re-self.im*b.im,self.re*b.im+self.im*b.re)
    __rmul__=__mul__
    def __truediv__(self,b):
        if not isinstance(b,C):return C(self.re/I(b),self.im/I(b))
        return self*C(b.re,-b.im)/(b.re*b.re+b.im*b.im)
    def __pow__(self,n):
        y=C(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return UP.add(self.re.ab(),self.im.ab())
    def exp(self):
        if self.im.lo==self.im.hi==0:return C(ex(self.re))
        co,si=cs(self.im);e=ex(self.re);return C(e*co,e*si)
    def widen(self,e):return C(self.re.widen(e),self.im.widen(e))
    def __repr__(self):return 'Re='+repr(self.re)+'; Im='+repr(self.im)

def polys(m):
    p=[F(0),F(-6),F(4)];out=[p]
    for j in range(m):
        q=[F(0)]*(len(p)+1)
        for k,t in enumerate(p):q[k]+=(F(1,2)+2*k)*t;q[k+1]-=2*t
        p=q;out.append(p)
    return out
PS=polys(14)
NTHETA=12

def evalp(p,z):
    out=C(0)
    for q in reversed(p):out=out*z+I(q)
    return out

def phi_jets(z,order=14):
    z=C(z);aa=PI*(2*z).exp();lead=(z/2).exp();out=[C(0) for _ in range(order+1)]
    for n in range(1,NTHETA+1):
        v=aa*(n*n);e=(-v).exp()
        for j in range(order+1):out[j]=out[j]+evalp(PS[j],v)*e
    return [lead*t for t in out]

def midpoint_integral(zscale,length,count):
    # Integral of 2*zscale^2*s*Phi_N(zscale*s)^2 ds.
    scale=C(zscale);h=F(length,2*count);result=C(0)
    for k in range(count):
        s=F(length*(2*k+1),2*count);jets=phi_jets(scale*I(s))
        jet=[v*(scale**j)/factorial(j) for j,v in enumerate(jets)]
        sq=[sum((jet[k]*jet[j-k] for k in range(j+1)),C(0)) for j in range(15)]
        coeff=[2*(scale**2)*(I(s)*sq[j]+(sq[j-1] if j else C(0))) for j in range(15)]
        result=result+sum((coeff[j]*I(2*h**(j+1)/F(j+1)) for j in range(0,15,2)),C(0))
    return result

# Exact algebra plants before any target certificate.
assert (I(F(1,3))*3).lo<=1<=(I(F(1,3))*3).hi
assert (C(1,2)*C(3,-4)).re.lo<=11<=(C(1,2)*C(3,-4)).re.hi
assert (C(1,2)*C(3,-4)).im.lo<=2<=(C(1,2)*C(3,-4)).im.hi
co,si=cs(PI/2);assert co.lo<=0<=co.hi and si.lo<=1<=si.hi
# K=1+xy, w=sqrt(1+x^2)sqrt(1+y^2), null row (1,-2,1) at -1,0,1.
assert sum((a*b*(1+x*y) for a,x in [(1,-1),(-2,0),(1,1)] for b,y in [(1,-1),(-2,0),(1,1)]))==0
assert (I(2)**2).lo>0  # 2sqrt(2)-2 is nonzero; square parity is independent of numerics.
print('ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS',flush=True)
center=C(I(F(237019,10**6)),I(F(715864,10**6)))
r=F(1,100000)
# Source-series tail on the actual slanted path and the root box.
end_a=PI*(2*center).exp()
assert end_a.re.lo>D('0.6')
assert center.re.hi<D('0.24') and center.im.hi<D('0.72')
assert (PI*ex(I('0.48'))).hi<6
# log(e^(2as)cos(2bs)) is concave on [0,1], so endpoint minima pay the path.
T0=4*sum(abs(q) for q in PS[0])*6**2*13**4*ex(I(F(-507,5)))
T1=4*sum(abs(q) for q in PS[1])*6**3*13**6*ex(I(F(-507,5)))
# Polynomial/geometric majorants, with ratio at n=13 already below 1/2.
ratio=I(F(14,13))**6*ex(I(F(-81,5)))
assert ratio.hi<F(1,2)
complex_source_error=(2*T0*(2*2**16+T0)).hi
assert complex_source_error<D('1e-25')
real_tail=20*3**3*13**6*ex(-507)
assert (9*real_tail*(2*2048+real_tail)).hi<D('1e-100')
# Analytic tube bounds: radius 1/32 in the integration variable.
# Complex segment: Re(z)>=-1/32, Re(z)<=0.24+1/32, |Im(z)|<=0.72+1/32.
# |center|<19/25, so the s-tube has z-width at most 19/800.
assert (center.re*center.re+center.im*center.im).hi<D('0.5776')
maxim=center.im+I(F(19,800))
qmin=PI*ex(I(F(-19,400)))*cs(2*maxim)[0]
assert qmin.lo>D('0.25')
qmax=PI*ex(2*(center.re+I(F(19,800))))
assert qmax.hi<7
# Uniform absolute theta bounds used for the Cauchy remainders are paper-proved.
real=midpoint_integral(C(1),3,384)
real_err=I(3*F(2**25)*F(1,8)**16/F(7,8)+F(1,10**90)).hi
real=real.widen(real_err)
print('RAW_D0='+repr(real.re),flush=True)
slant=midpoint_integral(center,1,128)
slant_err=I(F(2**34)*F(1,8)**16/F(7,8)+F(1,10**25)).hi
slant=slant.widen(slant_err)
value=real-slant
print('RAW_D_AT_CENTER='+repr(value),flush=True)
print('D0_CAUCHY_ERROR_UPPER='+str(real_err),flush=True)
print('SLANT_CAUCHY_ERROR_UPPER='+str(slant_err),flush=True)
assert value.ab()<D('0.01')
p,p1=phi_jets(center,1)
p=p.widen(T0.hi);p1=p1.widen(T1.hi)
dp=-2*center*p*p
# lower absolute squared bounds from the rectangular enclosure.
def sq_lower(a):
    if a.lo<=0<=a.hi:return D(0)
    x=min(abs(a.lo),abs(a.hi));return DOWN.multiply(x,x)
lowdp=DOWN.add(sq_lower(dp.re),sq_lower(dp.im))
print('RAW_DPRIME='+repr(dp),flush=True)
print('DPRIME_MODULUS_SQUARED_LOWER='+str(lowdp),flush=True)
assert lowdp>D(9000**2)
box=C(center.re.widen(I(r).hi),center.im.widen(I(r).hi))
ba=PI*(2*box).exp();assert ba.re.lo>D('0.6') and ba.ab()<6
p,p1=phi_jets(box,1);p=p.widen(T0.hi);p1=p1.widen(T1.hi)
M2=(2*I(p.ab())**2+4*I(box.ab())*I(p.ab())*I(p1.ab())).hi
print('DSECOND_MODULUS_UPPER='+str(M2),flush=True)
assert M2<D(10**8)
margin=F(9000)*r-F(1,100)-F(10**8,2)*r*r
assert margin==F(3,40)>0
print('ROUCHE_MARGIN_LOWER='+str(margin),flush=True)
print('ONE_SIMPLE_ZERO_IN_CENTER_RADIUS_1e-5=PASS',flush=True)
print('NO_ASSERTION_OF_V_NEGATIVITY_OR_RH',flush=True)
```

### A60. Буквальный stdout, precision60

```text
ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS
RAW_D0=[0.0402423013541951961103084592132460220280240264010075957485743, 0.0402431187893235443245941734989603077423097406867218814629154]
RAW_D_AT_CENTER=Re=[-0.0021128320791154352145889098469739957336781718382352829918000, -0.0019725057154156584288744241326882814479638861239495645860203]; Im=[-0.000352654740384315654216979567931157513508143257399274377957144, -0.000212328376684538868502493853645443227793857543113555970942856]
D0_CAUCHY_ERROR_UPPER=4.08717564174107142857142857142857142857142857142857142857143E-7
SLANT_CAUCHY_ERROR_UPPER=0.0000697544642857142857143857142857142857142857142857142857142858
RAW_DPRIME=Re=[-10208.1854149345727087293141600225159058297287390403555070396, -10208.1854149345727087293141600225159055337811156094608283392]; Im=[134.92315134372579133955023347503502456994827332403430232152, 134.92315134372579133955023347503502486589589675492898102230]
DPRIME_MODULUS_SQUARED_LOWER=104225253.722451456318832685389511139877454623970977941949498
DSECOND_MODULUS_UPPER=3295146.68800746613899181738869160976373021393571183621029615
ROUCHE_MARGIN_LOWER=3/40
ONE_SIMPLE_ZERO_IN_CENTER_RADIUS_1e-5=PASS
NO_ASSERTION_OF_V_NEGATIVITY_OR_RH
```

### A90. Буквальный stdout, precision90

```text
ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS
RAW_D0=[0.0402423013541951961103084592132460220280240264010075957485927046764294967326539930131642794, 0.0402431187893235443245941734989603077423097406867218814628784189621437824469397072988786223]
RAW_D_AT_CENTER=Re=[-0.0021128320791154352145889098469739957336781718382352809050655110204193480670209210469347749, -0.0019725057154156584288744241326882814479638861239495666193512253008597555396442280484777134]; Im=[-0.000352654740384315654216979567931157513508143257399272314114078084670534776590104209356858144, -0.000212328376684538868502493853645443227793857543113558028399792365103147747300819438874641856]
D0_CAUCHY_ERROR_UPPER=4.08717564174107142857142857142857142857142857142857142857142857142857142857142857143857143E-7
SLANT_CAUCHY_ERROR_UPPER=0.0000697544642857142857143857142857142857142857142857142857142857142857142857142857142857142858
RAW_DPRIME=Re=[-10208.1854149345727087293141600225159058297287390403555069169104382866296164805737151500652, -10208.1854149345727087293141600225159055337811156094608284637535200554404895085409271747440]; Im=[134.92315134372579133955023347503502456994827332403430244580121522110779167423912298253014, 134.92315134372579133955023347503502486589589675492898089895813345229763683735045259595651]
DPRIME_MODULUS_SQUARED_LOWER=104225253.722451456318832685389511139877454623970977941952075760383679528134348439046426795
DSECOND_MODULUS_UPPER=3295146.68800746613899181738869160976373021393571183621026658821080530765433898444152775266
ROUCHE_MARGIN_LOWER=3/40
ONE_SIMPLE_ZERO_IN_CENTER_RADIUS_1e-5=PASS
NO_ASSERTION_OF_V_NEGATIVITY_OR_RH
```

Оба stderr пусты. Совпадение строгих рациональных выводов на двух точностях — повтор одного сертификата, не вторая независимая математическая проверка.

## Appendix B. Диагностические запуски, не доказательство

Следующие конечные вычисления нужны лишь для выбора центра (2). Их ошибки не сертифицированы. Они не входят в доказательную цепь (11)--(16). Все числа, названные малыми или нулевыми этими запусками, остаются диагностикой. `N` в них — конечное число theta-мод; это НЕ полный источник без остатка.

### Первый Newton: сходимость к нулю не установлена

Команда: `python /mnt/data/thetarf/diagnostic_diagonal.py`.

```python
"""Non-certified complex diagonal diagnostic; not a theta sign proof."""
import mpmath as m
m.mp.dps=30
N=12

def phi(z):
    a=m.pi*m.exp(2*z)
    return m.exp(z/2)*sum((4*(n*n*a)**2-6*n*n*a)*m.exp(-n*n*a) for n in range(1,N+1))
D0=m.quad(lambda t:2*t*phi(t)**2,[0,m.mpf('.25'),m.mpf('.5'),1,2,3])
def D(z):
    return D0-2*z*z*m.quad(lambda s:s*phi(s*z)**2,[0,1])
def Dprime(z):
    return -2*z*phi(z)**2
print('DIAGNOSTIC_ONLY; theta_modes=12; precision=30; integrals_truncated_at_3; NO_ERROR_CERTIFICATE',flush=True)
print('D0='+m.nstr(D0,25),flush=True)
z=m.mpc('.3','.6')
for j in range(12):
    d=D(z); step=d/Dprime(z)
    print(j,m.nstr(z,22),m.nstr(abs(d),12),flush=True)
    # Deterministic trust-region Newton, never leave the source strip.
    fac=m.mpf(1)
    while abs(step*fac)>m.mpf('.15') or abs(m.im(z-step*fac))>=m.mpf('.77'):
        fac/=2
    z-=fac*step
print('FINAL='+m.nstr(z,25),flush=True)
```

Буквальный stdout:

```text
DIAGNOSTIC_ONLY; theta_modes=12; precision=30; integrals_truncated_at_3; NO_ERROR_CERTIFICATE
D0=0.04024271007175937021745132
0 (0.3 + 0.6j) 18.2124300057
1 (0.2992984801037574785829 + 0.5552606426189149802845j) 6.74048883899
2 (0.3032019923933237084971 + 0.5101552541603984887335j) 2.50605274497
3 (0.3110840332676196165936 + 0.464588326679246766905j) 0.933611454747
4 (0.3233380158803121921986 + 0.4188498920113746031961j) 0.347245904365
5 (0.340450517385002412015 + 0.373723096307850777455j) 0.128572325807
6 (0.3626546623802149147617 + 0.3303997276953340242292j) 0.0472541977774
7 (0.3896480282965263686644 + 0.2903172870948182261221j) 0.0171955812804
8 (0.4204189472903543798995 + 0.2547831665782032224026j) 0.00619044941754
9 (0.4534218203491274591243 + 0.2245028167341051910357j) 0.00220856882005
10 (0.4870779884873588843764 + 0.1993913352758804990323j) 0.000783522561189
11 (0.5202038400740451036481 + 0.178805853447665023161j) 0.000277319961582
FINAL=(0.5521122256238215628031469 + 0.1619150048956192937533918j)
```

### Грубая дуга: недопустимый отрицательный winding; INVALID_AS_A_ZERO_COUNT

Команда: `python /mnt/data/thetarf/diagnostic_contour.py`.

```python
"""One non-certified argument diagnostic for the same analytic divisor test."""
import mpmath as m
m.mp.dps=35
N=24
R=m.mpf(3)/4

def phi(z):
    a=m.pi*m.exp(2*z)
    return m.exp(z/2)*sum((4*(n*n*a)**2-6*n*n*a)*m.exp(-n*n*a) for n in range(1,N+1))
D0=m.quad(lambda t:2*t*phi(t)**2,[0,m.mpf('.25'),m.mpf('.5'),1,2,3])
def D(z):
    return D0-2*z*z*m.quad(lambda s:s*phi(s*z)**2,[0,m.mpf('.5'),1])
print('DIAGNOSTIC_ONLY; theta_modes=24; dps=35; one quadrant circular arc radius=3/4; NO_ERROR_CERTIFICATE',flush=True)
last=0; total=m.mpf(0)
for j in range(33):
    z=R*m.exp(1j*m.pi*j/64)
    a=m.arg(D(z))
    delta=a-last
    while delta>m.pi:delta-=2*m.pi
    while delta<-m.pi:delta+=2*m.pi
    total+=delta;last=a
    print(j,m.nstr(z,15),m.nstr(a,12),m.nstr(total/m.pi,12),flush=True)
print('QUADRANT_UNWRAPPED_PI='+m.nstr(total/m.pi,20),flush=True)
```

Буквальный stdout:

```text
DIAGNOSTIC_ONLY; theta_modes=24; dps=35; one quadrant circular arc radius=3/4; NO_ERROR_CERTIFICATE
0 (0.75 + 0.0j) 0.0 0.0
1 (0.749096592153879 + 0.0368007557455635j) -1.75700235825 -0.55927122068
2 (0.746388545004148 + 0.0735128552471705j) 2.80696788455 -1.10651437215
3 (0.741882382473586 + 0.110047855841521j) 1.16192902652 -1.63014650382
4 (0.735588960302423 + 0.146317741512096j) -0.375261981381 -2.11944959858
5 (0.727523439895908 + 0.182235134927448j) -1.77481693757 -2.5649417774
6 (0.717705251799157 + 0.217713507940847j) -3.01178322652 -2.95868037605
7 (0.706158048887266 + 0.252667390044165j) 2.21644836364 -3.29448257364
8 (0.692909649383465 + 0.287012574273817j) 1.35699416379 -3.56805534217
9 (0.677991969842582 + 0.320666320072712j) 0.700471841257 -3.77703288793
10 (0.661440948261266 + 0.353547552619498j) 0.248418648439 -3.92092588829
11 (0.643296457500204 + 0.385577058144916j) -0.00311701726925 -4.00099217741
12 (0.623602209226909 + 0.416677674764702j) -0.0629660181033 -4.02004270606
13 (0.602405648610484 + 0.446774478369325j) 0.0559224057237 -3.9821993454
14 (0.579757840022053 + 0.475794963122734j) 0.337336952398 -3.89262231308
15 (0.555713344016219 + 0.503669216135264j) 0.762701906667 -3.7572244429
16 (0.530330085889911 + 0.530330085889911j) 1.31197415727 -3.58238565532
17 (0.503669216135264 + 0.555713344016219j) 1.96451430421 -3.37467567542
18 (0.475794963122734 + 0.579757840022053j) 2.69966123484 -3.1406711396
19 (0.446774478369325 + 0.602405648610484j) -2.7877888508 -2.8873807518
20 (0.416677674764702 + 0.623602209226909j) -1.95776366313 -2.62317552879
21 (0.385577058144916 + 0.643296457500204j) -1.10397724917 -2.35140687253
22 (0.353547552619498 + 0.661440948261266j) -0.157305122932 -2.05007177578
23 (0.320666320072712 + 0.677991969842582j) 0.974400047285 -1.68983883185
24 (0.287012574273817 + 0.692909649383465j) 2.03704512787 -1.3515883972
25 (0.252667390044165 + 0.706158048887266j) 2.05833987039 -1.34481007013
26 (0.217713507940847 + 0.717705251799157j) 1.05796085653 -1.66324060017
27 (0.182235134927448 + 0.727523439895908j) 2.97244325169 -1.05384192687
28 (0.146317741512096 + 0.735588960302423j) -2.17117714283 -0.691107149219
29 (0.110047855841521 + 0.741882382473586j) -0.0652371454202 -0.0207656283337
30 (0.0735128552471705 + 0.746388545004148j) -2.97848429155 -0.948080995843
31 (0.0368007557455635 + 0.749096592153879j) 1.69978385974 -1.45894199307
32 (-2.06474738928305e-37 + 0.75j) 7.46701881577e-38 -2.0
QUADRANT_UNWRAPPED_PI=-2.0
```

### Недемпфированный новый seed того же объекта: сходимость не установлена

Команда: `python /mnt/data/thetarf/diagnostic_divisor_seed.py`.

```python
"""Non-certified complex diagonal diagnostic; not a theta sign proof."""
import mpmath as m
m.mp.dps=40
N=24

def phi(z):
    a=m.pi*m.exp(2*z)
    return m.exp(z/2)*sum((4*(n*n*a)**2-6*n*n*a)*m.exp(-n*n*a) for n in range(1,N+1))
D0=m.quad(lambda t:2*t*phi(t)**2,[0,m.mpf('.25'),m.mpf('.5'),1,2,3])
def D(z):
    return D0-2*z*z*m.quad(lambda s:s*phi(s*z)**2,[0,1])
def Dprime(z):
    return -2*z*phi(z)**2
print('DIAGNOSTIC_ONLY; theta_modes=24; precision=40; integrals_truncated_at_3; NO_ERROR_CERTIFICATE',flush=True)
print('D0='+m.nstr(D0,25),flush=True)
z=m.mpc('.25','.7')
for j in range(12):
    d=D(z); step=d/Dprime(z)
    print(j,m.nstr(z,22),m.nstr(abs(d),12),flush=True)
    # Deterministic trust-region Newton, never leave the source strip.
    fac=m.mpf(1)
    while abs(step*fac)>m.mpf('.15') or abs(m.im(z-step*fac))>=m.mpf('.77'):
        fac/=2
    z-=fac*step
print('FINAL='+m.nstr(z,25),flush=True)
```

Буквальный stdout:

```text
DIAGNOSTIC_ONLY; theta_modes=24; precision=40; integrals_truncated_at_3; NO_ERROR_CERTIFICATE
D0=0.04024271007175937021745132
0 (0.25 + 0.7j) 67.5758769111
1 (0.1371497506735050707984 + 0.7687729318327158737932j) 52258.9878575
2 (0.1352708399320386152827 + 0.7658089835896162462192j) 21940.6738025
3 (0.1315220357683044648351 + 0.7628115499273523483196j) 11359.7957768
4 (0.1186177822636713309011 + 0.7600720985751761129827j) 11987.9852672
5 (0.1299307170986210423037 + 0.7524947265257374990192j) 6783.12033967
6 (0.1310434788911686117652 + 0.7358647221678884529196j) 2390.01618834
7 (0.1349962789038460977227 + 0.7198998954674919739913j) 957.173920984
8 (0.138293337975908751208 + 0.7005468837232861521448j) 381.369096288
9 (0.1393097286207373310328 + 0.6776034454117631167947j) 151.747148342
10 (0.1375457906038666056659 + 0.6505697694790718503034j) 61.4585104373
11 (0.1320291799188945023901 + 0.6178183502396708818937j) 25.2691665386
FINAL=(0.1221721598480612756300507 + 0.5770047475209691814139975j)
```

### Safeguarded Newton: только выбор рационального центра

Команда: `python /mnt/data/thetarf/diagnostic_divisor_damped.py`.

```python
"""Same divisor diagnostic; safeguarded Newton. No certificate is claimed."""
import mpmath as m
m.mp.dps=35
N=24

def phi(z):
    a=m.pi*m.exp(2*z)
    return m.exp(z/2)*sum((4*(n*n*a)**2-6*n*n*a)*m.exp(-n*n*a) for n in range(1,N+1))
D0=m.quad(lambda t:2*t*phi(t)**2,[0,m.mpf('.25'),m.mpf('.5'),1,2,3])
def D(z):
    return D0-2*z*z*m.quad(lambda s:s*phi(s*z)**2,[0,m.mpf('.5'),1])
z=m.mpc('.25','.7')
print('DIAGNOSTIC_ONLY; full-theta truncation N=24; dps=35; no error certificate',flush=True)
for k in range(24):
    val=D(z); dp=-2*z*phi(z)**2; step=val/dp
    print(k,m.nstr(z,20),m.nstr(abs(val),10),m.nstr(abs(step),10),flush=True)
    if abs(step)<m.mpf('1e-22'):break
    t=m.mpf(1)
    accepted=False
    for j in range(24):
        zz=z-t*step
        if 0<m.re(zz)<m.mpf('.6') and 0<m.im(zz)<m.mpf('.77'):
            vv=D(zz)
            if abs(vv)<abs(val):
                z=zz;accepted=True;break
        t/=2
    if not accepted:
        print('LINE_SEARCH_STOP',flush=True);break
print('FINAL='+m.nstr(z,30),flush=True)
```

Буквальный stdout:

```text
DIAGNOSTIC_ONLY; full-theta truncation N=24; dps=35; no error certificate
0 (0.25 + 0.7j) 67.57587691 0.2643096285
1 (0.23589371883418813385 + 0.70859661647908948422j) 50.69325092 0.0110451938
2 (0.2383546092719710578 + 0.71354061230769832012j) 23.09533097 0.003215776961
3 (0.23667163279401765998 + 0.71628083340034102842j) 5.725352591 0.0005250084017
4 (0.23700264771517764153 + 0.71587332518715121116j) 0.1907433058 1.864904493e-5
5 (0.23701877797191769856 + 0.71586396560947327895j) 0.0002317226007 2.26975803e-8
6 (0.23701880029967075782 + 0.71586396969010982137j) 3.429128442e-10 3.358884907e-14
7 (0.23701880029967002202 + 0.71586396969014340216j) 7.509566492e-22 7.355737755e-26
FINAL=(0.23701880029967002201662409766 + 0.715863969690143402162895473649j)
```

## Appendix C. Байтовая проверка доступных frames и рациональных констант

Команда: `python /mnt/data/thetarf/check_transport_and_constants.py`. ROOT — папка с исходными TXT, WORK — рабочая папка отчёта; при переносе измени только эти пути, например `ROOT=Path("/tmp/source_bundle")`, `WORK=ROOT/"thetarf"`, создав `WORK/"sources"`. Это транспорт/арифметика констант, не дополнительный source-sign опыт.

```python
"""Byte checks and rational proof-budget checks; not a theta sign scan."""
from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import hashlib, sys, decimal
ROOT=Path('/mnt/data'); WORK=ROOT/'thetarf'

def frame(packet,path,size):
    lines=packet.read_bytes().splitlines(keepends=True)
    marker=('===== FILE '+path+' BYTES ').encode()
    i=next(i for i,s in enumerate(lines) if s.startswith(marker))+1
    out=bytearray()
    while len(out)<size:
        assert lines[i].startswith(b'| ')
        out.extend(lines[i][2:]);i+=1
    assert len(out)==size
    return bytes(out)

def check(name,data,size,lf,sha,blob):
    got=hashlib.sha256(data).hexdigest()
    git=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert (len(data),data.count(b'\n'),data.count(b'\r'),data.endswith(b'\n'))==(size,lf,0,True)
    assert (got,git)==(sha,blob)
    print(name, 'BYTES='+str(size),'LF='+str(lf),'SHA256='+got,'BLOB='+git,'MATCH')
    (WORK/'sources'/name).write_bytes(data)

for name,packet,path,size,lf,sha,blob in [
 ('W.md','PROSHKA_REQUEST_GOAL058_ODDINFINITY_2026-09-12.txt',
 'docs/Codex/REPORT_2026-09-12_FULL_SIGN_TRANSFER_AUDIT.md',15303,335,
 '1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282','b8b5a1a8739c946f75340f3115616d6f9ba5b40e'),
 ('S.md','PROSHKA_REQUEST_GOAL058_ODD2COMPACT_2026-09-12.txt',
 'docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md',37796,467,
 '14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc','de9578084446baecfbb2a316d7bda3da817c8c01')]:
    check(name,frame(ROOT/packet,path,size),size,lf,sha,blob)

r=Q(1,100000); a=Q(237019,10**6); b=Q(715864,10**6)
assert a*a+b*b<Q(759,1000)**2
assert Q(759,1000)+r<Q(19,25)<Q(77,100)
x=Q(77,50)
cos_lower=sum(((-1)**k*x**(2*k)/factorial(2*k) for k in range(4)),Q(0))
assert cos_lower>Q(3,100)
assert 5400*800**2*20<2**37
assert 2*factorial(5)*100**6<2**48
assert Q(77,100)**2/(2*Q(9,5))<Q(1,6)
assert 1-Q(77,100)**2/2>Q(7,10)
assert 2*(4*7**2*128+6*7*12)<2**16
assert 9000*r-Q(1,100)-Q(10**8,2)*r*r==Q(3,40)>0
print('DISC_INCLUSION=PASS; COS_1_54_LOWER='+str(cos_lower))
print('CAUCHY_KERNEL_BOUND=2^122; CHANNEL_NONVANISHING_BOUNDS=PASS')
print('ROUCHE_RATIONAL_MARGIN=3/40')
print('PYTHON='+sys.version.split()[0]+'; LIBMPDEC='+decimal.__libmpdec_version__)
for name in ['preregistration.txt','certify_divisor.py','certify60.stdout','certify90.stdout']:
    data=(WORK/name).read_bytes()
    print(name,'BYTES='+str(len(data)),'SHA256='+hashlib.sha256(data).hexdigest())
print('R,I,C,A,L: remote Git blobs checked; SHA256/byte counts inherited from pinned request, not locally rehashed')
```

Буквальный stdout:

```text
W.md BYTES=15303 LF=335 SHA256=1e296a504631b58beb7863f4c7f36174bd08876cfc7093febfe00cc8306a5282 BLOB=b8b5a1a8739c946f75340f3115616d6f9ba5b40e MATCH
S.md BYTES=37796 LF=467 SHA256=14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc BLOB=de9578084446baecfbb2a316d7bda3da817c8c01 MATCH
DISC_INCLUSION=PASS; COS_1_54_LOWER=337805694911/11250000000000
CAUCHY_KERNEL_BOUND=2^122; CHANNEL_NONVANISHING_BOUNDS=PASS
ROUCHE_RATIONAL_MARGIN=3/40
PYTHON=3.13.5; LIBMPDEC=2.5.1
preregistration.txt BYTES=1347 SHA256=a76d72c0e99c5a13a1b2a83095d753ec42d46199008d5394856af066a68f7afc
certify_divisor.py BYTES=8994 SHA256=578dcb6eb0705c93fe26c5668f960e9789fd276df0220055f62bba89adab52a8
certify60.stdout BYTES=1207 SHA256=1ca45a858a318fc136089ebb613fc803748e138a0bc050609abebc8239db9013
certify90.stdout BYTES=1627 SHA256=db2cc93b85553e3f11276fa1f65d44b062c12b5a1ff846bcfdc287a67541e0cf
R,I,C,A,L: remote Git blobs checked; SHA256/byte counts inherited from pinned request, not locally rehashed
```

До объединённой проверки отдельно выполнено следующее рациональное сравнение; float выводится только как diagnostic.

```python
from fractions import Fraction as Q
from math import factorial
x=Q(77,50)
c=sum(((-1)**k*x**(2*k)/factorial(2*k) for k in range(4)),Q(0))
print(c, float(c), 'above .03:', c>Q(3,100))
```

```text
337805694911/11250000000000 0.030027172880977778 above .03: True
```

## Appendix D. Полная сохранённая регистрация и судьба предсказаний

```text
REQ-2026-09-13-THETARF, resumed without changing T12/T13.
Named test: ANALYTIC_SQUARE_ROOT_DIVISOR_OBSTRUCTION.
Registration precedes new source evaluation.
P1 (0.60): D(z)=V(z,z) has an odd-order nonreal zero in |Im z|<pi/4.
Discriminator: a full-source Rouche/argument-principle certificate, not a small floating value.
P2 (0.90): if such a zero exists and an independent nonzero channel of J
extends across it, domination V>=delta W for any delta>0 is impossible
by holomorphic extension of dominated features and parity of zero orders.
Control: K(z,w)=1+zw has a positive real restriction, while sqrt(1+x^2)
can have no bounded rank-one domination by K; do not turn this into K<0.
Use one deterministic complex diagonal test, not a node/Hankel/random sweep.
If no zero is certified, keep the actual RF question unresolved.
No RH, real-zero, simple-zero or target positivity premise is imported.
Continuation of the SAME divisor test after the first diagnostics:
The first Newton path escaped toward the real tail and certifies no zero.
A coarse one-quadrant contour returned an impossible negative winding count;
it is explicitly INVALID_AS_A_ZERO_COUNT (insufficient phase resolution).
One interior Newton seed 1/4+7i/10 is chosen to test the oscillatory arc region.
Only a subsequent fully bounded analytic certificate may establish a zero.
```

Первоначальный файл имел SHA256 `313e63d277103a7cc5d34f8d3e7c570fb1a489ce7dbe56346781bacbfdaf8740`; после явно обозначенного дополнения — `a76d72c0e99c5a13a1b2a83095d753ec42d46199008d5394856af066a68f7afc`. Хеш подтверждает байты, но сам по себе не доказывает время регистрации для внешнего проверяющего. Заявленная последовательность операций — producer provenance, не независимая timestamp-квитанция.

## Appendix E. Сохранённая первая версия с техническим TypeError

Ниже полный исходник первого запуска, сохранённый после отказа как `certify_divisor_transport_typeerror.py`. Во время отказа он исполнялся командой `python /mnt/data/thetarf/certify_divisor.py 60`. Эта версия НЕ является сертификатом. Её единственный stdout предшествует целевому вычислению; следующая ошибка привела к двум dispatch-поправкам, видимым сравнением с Appendix A.

```python
"""Directed-Decimal certificate for one zero of the full theta diagonal.
No xi zeros, source node matrices, or target positivity are used.
"""
from decimal import Decimal as D, Context, getcontext, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as F
from math import factorial, comb
import sys
PREC = int(sys.argv[1]) if len(sys.argv)>1 else 60
getcontext().prec=PREC
DOWN=Context(prec=PREC,rounding=ROUND_FLOOR,Emin=-999999,Emax=999999)
UP=Context(prec=PREC,rounding=ROUND_CEILING,Emin=-999999,Emax=999999)
NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN,Emin=-999999,Emax=999999)
class I:
    __slots__=('lo','hi')
    def __init__(self,lo=0,hi=None):
        if isinstance(lo,I): self.lo,self.hi=lo.lo,lo.hi;return
        if isinstance(lo,F):
            self.lo=DOWN.divide(D(lo.numerator),D(lo.denominator));self.hi=UP.divide(D(lo.numerator),D(lo.denominator));return
        self.lo=D(lo);self.hi=D(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,b):
        b=I(b);return I(DOWN.add(self.lo,b.lo),UP.add(self.hi,b.hi))
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,b):return self+-I(b)
    def __rsub__(self,b):return I(b)+-self
    def __mul__(self,b):
        b=I(b);p=[(x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I(min(DOWN.multiply(x,y) for x,y in p),max(UP.multiply(x,y) for x,y in p))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b);assert not b.lo<=0<=b.hi
        return self*I(DOWN.divide(D(1),b.hi),UP.divide(D(1),b.lo))
    def __rtruediv__(self,b):return I(b)/self
    def __pow__(self,n):
        assert n>=0 and isinstance(n,int)
        y=I(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return max(abs(self.lo),abs(self.hi))
    def __repr__(self):return '['+str(self.lo)+', '+str(self.hi)+']'
    def widen(self,e):return self+I(-e,e)
ZERO=I(0)

def ex(a):
    a=I(a)
    return I(NEAR.next_minus(NEAR.exp(a.lo)),NEAR.next_plus(NEAR.exp(a.hi)))

def atan_recip(q,n):
    s=sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(n)),F(0))
    e=F(1,(2*n+1)*q**(2*n+1))
    return (s,s+e) if n%2==0 else (s-e,s)
a,b=atan_recip(5,100);c,d=atan_recip(239,30)
PILO,PIHI=16*a-4*d,16*b-4*c
PI=I(I(PILO).lo,I(PIHI).hi)
assert PI.lo>D('3.14159') and PI.hi<D('3.14160')

def cs(a):
    a=I(a)
    mid=NEAR.divide(NEAR.add(a.lo,a.hi),D(2))
    rad=max(UP.subtract(mid,a.lo),UP.subtract(a.hi,mid))
    if rad>=1:return I(-1,1),I(-1,1)
    period=NEAR.multiply(D(2),NEAR.divide(NEAR.add(PI.lo,PI.hi),D(2)))
    k=int(NEAR.divide(mid,period).to_integral_value(rounding=ROUND_HALF_EVEN))
    x=I(mid)-2*k*PI
    assert x.ab()<D(4)
    xx=x*x;tc=I(1);ts=x;co=tc;si=ts
    # Terms through degree 79; a uniform absolute tail below 1e-65.
    for j in range(1,40):
        tc=-tc*xx/((2*j-1)*(2*j));ts=-ts*xx/((2*j)*(2*j+1))
        co=co+tc;si=si+ts
    # For |x|<=4 the remaining successive-term ratio is below 1/2.
    rem=I(F(2*4**80,factorial(80))).hi
    e=UP.add(rad,rem)
    co=co.widen(e);si=si.widen(e)
    return I(max(co.lo,D(-1)),min(co.hi,D(1))),I(max(si.lo,D(-1)),min(si.hi,D(1)))
class C:
    __slots__=('re','im')
    def __init__(self,re=0,im=0):
        if isinstance(re,C):self.re,self.im=re.re,re.im;return
        self.re=I(re);self.im=I(im)
    def __add__(self,b):b=C(b);return C(self.re+b.re,self.im+b.im)
    __radd__=__add__
    def __neg__(self):return C(-self.re,-self.im)
    def __sub__(self,b):return self+-C(b)
    def __rsub__(self,b):return C(b)+-self
    def __mul__(self,b):
        b=C(b)
        if self.im.lo==self.im.hi==0 and b.im.lo==b.im.hi==0:return C(self.re*b.re)
        return C(self.re*b.re-self.im*b.im,self.re*b.im+self.im*b.re)
    __rmul__=__mul__
    def __truediv__(self,b):
        if not isinstance(b,C):return C(self.re/I(b),self.im/I(b))
        return self*C(b.re,-b.im)/(b.re*b.re+b.im*b.im)
    def __pow__(self,n):
        y=C(1);x=self
        while n:
            if n&1:y=y*x
            x=x*x;n//=2
        return y
    def ab(self):return UP.add(self.re.ab(),self.im.ab())
    def exp(self):
        if self.im.lo==self.im.hi==0:return C(ex(self.re))
        co,si=cs(self.im);e=ex(self.re);return C(e*co,e*si)
    def widen(self,e):return C(self.re.widen(e),self.im.widen(e))
    def __repr__(self):return 'Re='+repr(self.re)+'; Im='+repr(self.im)

def polys(m):
    p=[F(0),F(-6),F(4)];out=[p]
    for j in range(m):
        q=[F(0)]*(len(p)+1)
        for k,t in enumerate(p):q[k]+=(F(1,2)+2*k)*t;q[k+1]-=2*t
        p=q;out.append(p)
    return out
PS=polys(14)
NTHETA=12

def evalp(p,z):
    out=C(0)
    for q in reversed(p):out=out*z+I(q)
    return out

def phi_jets(z,order=14):
    z=C(z);aa=PI*(2*z).exp();lead=(z/2).exp();out=[C(0) for _ in range(order+1)]
    for n in range(1,NTHETA+1):
        v=aa*(n*n);e=(-v).exp()
        for j in range(order+1):out[j]=out[j]+evalp(PS[j],v)*e
    return [lead*t for t in out]

def midpoint_integral(zscale,length,count):
    # Integral of 2*zscale^2*s*Phi_N(zscale*s)^2 ds.
    scale=C(zscale);h=F(length,2*count);result=C(0)
    for k in range(count):
        s=F(length*(2*k+1),2*count);jets=phi_jets(scale*I(s))
        jet=[v*(scale**j)/factorial(j) for j,v in enumerate(jets)]
        sq=[sum((jet[k]*jet[j-k] for k in range(j+1)),C(0)) for j in range(15)]
        coeff=[2*(scale**2)*(I(s)*sq[j]+(sq[j-1] if j else C(0))) for j in range(15)]
        result=result+sum((coeff[j]*I(2*h**(j+1)/F(j+1)) for j in range(0,15,2)),C(0))
    return result

# Exact algebra plants before any target certificate.
assert (I(F(1,3))*3).lo<=1<=(I(F(1,3))*3).hi
assert (C(1,2)*C(3,-4)).re.lo<=11<=(C(1,2)*C(3,-4)).re.hi
assert (C(1,2)*C(3,-4)).im.lo<=2<=(C(1,2)*C(3,-4)).im.hi
co,si=cs(PI/2);assert co.lo<=0<=co.hi and si.lo<=1<=si.hi
# K=1+xy, w=sqrt(1+x^2)sqrt(1+y^2), null row (1,-2,1) at -1,0,1.
assert sum((a*b*(1+x*y) for a,x in [(1,-1),(-2,0),(1,1)] for b,y in [(1,-1),(-2,0),(1,1)]))==0
assert (I(2)**2).lo>0  # 2sqrt(2)-2 is nonzero; square parity is independent of numerics.
print('ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS',flush=True)
center=C(I(F(237019,10**6)),I(F(715864,10**6)))
r=F(1,100000)
# Source-series tail on the actual slanted path and the root box.
end_a=PI*(2*center).exp()
assert end_a.re.lo>D('0.6')
assert center.re.hi<D('0.24') and center.im.hi<D('0.72')
assert (PI*ex(I('0.48'))).hi<6
# log(e^(2as)cos(2bs)) is concave on [0,1], so endpoint minima pay the path.
T0=4*sum(abs(q) for q in PS[0])*6**2*13**4*ex(I(F(-507,5)))
T1=4*sum(abs(q) for q in PS[1])*6**3*13**6*ex(I(F(-507,5)))
# Polynomial/geometric majorants, with ratio at n=13 already below 1/2.
ratio=I(F(14,13))**6*ex(I(F(-81,5)))
assert ratio.hi<F(1,2)
complex_source_error=(2*T0*(2*2**16+T0)).hi
assert complex_source_error<D('1e-25')
real_tail=20*3**3*13**6*ex(-507)
assert (9*real_tail*(2*2048+real_tail)).hi<D('1e-100')
# Analytic tube bounds: radius 1/32 in the integration variable.
# Complex segment: Re(z)>=-1/32, Re(z)<=0.24+1/32, |Im(z)|<=0.72+1/32.
# |center|<19/25, so the s-tube has z-width at most 19/800.
assert (center.re*center.re+center.im*center.im).hi<D('0.5776')
maxim=center.im+I(F(19,800))
qmin=PI*ex(I(F(-19,400)))*cs(2*maxim)[0]
assert qmin.lo>D('0.25')
qmax=PI*ex(2*(center.re+I(F(19,800))))
assert qmax.hi<7
# Uniform absolute theta bounds used for the Cauchy remainders are paper-proved.
real=midpoint_integral(C(1),3,384)
real_err=I(3*F(2**25)*F(1,8)**16/F(7,8)+F(1,10**90)).hi
real=real.widen(real_err)
print('RAW_D0='+repr(real.re),flush=True)
slant=midpoint_integral(center,1,128)
slant_err=I(F(2**34)*F(1,8)**16/F(7,8)+F(1,10**25)).hi
slant=slant.widen(slant_err)
value=real-slant
print('RAW_D_AT_CENTER='+repr(value),flush=True)
print('D0_CAUCHY_ERROR_UPPER='+str(real_err),flush=True)
print('SLANT_CAUCHY_ERROR_UPPER='+str(slant_err),flush=True)
assert value.ab()<D('0.01')
p,p1=phi_jets(center,1)
p=p.widen(T0.hi);p1=p1.widen(T1.hi)
dp=-2*center*p*p
# lower absolute squared bounds from the rectangular enclosure.
def sq_lower(a):
    if a.lo<=0<=a.hi:return D(0)
    x=min(abs(a.lo),abs(a.hi));return DOWN.multiply(x,x)
lowdp=DOWN.add(sq_lower(dp.re),sq_lower(dp.im))
print('RAW_DPRIME='+repr(dp),flush=True)
print('DPRIME_MODULUS_SQUARED_LOWER='+str(lowdp),flush=True)
assert lowdp>D(9000**2)
box=C(center.re.widen(I(r).hi),center.im.widen(I(r).hi))
ba=PI*(2*box).exp();assert ba.re.lo>D('0.6') and ba.ab()<6
p,p1=phi_jets(box,1);p=p.widen(T0.hi);p1=p1.widen(T1.hi)
M2=(2*I(p.ab())**2+4*I(box.ab())*I(p.ab())*I(p1.ab())).hi
print('DSECOND_MODULUS_UPPER='+str(M2),flush=True)
assert M2<D(10**8)
margin=F(9000)*r-F(1,100)-F(10**8,2)*r*r
assert margin==F(3,40)>0
print('ROUCHE_MARGIN_LOWER='+str(margin),flush=True)
print('ONE_SIMPLE_ZERO_IN_CENTER_RADIUS_1e-5=PASS',flush=True)
print('NO_ASSERTION_OF_V_NEGATIVITY_OR_RH',flush=True)
```

Буквальный stdout:

```text
ARITHMETIC_AND_RANK_ONE_DOMINATION_PLANTS=PASS
```

Буквальный stderr:

```text
Traceback (most recent call last):
  File "/mnt/data/thetarf/certify_divisor.py", line 155, in <module>
    end_a=PI*(2*center).exp()
          ~~^~~~~~~~~~~~~~~~~
  File "/mnt/data/thetarf/certify_divisor.py", line 28, in __mul__
    b=I(b);p=[(x,y) for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
  File "/mnt/data/thetarf/certify_divisor.py", line 19, in __init__
    self.lo=D(lo);self.hi=D(lo if hi is None else hi)
            ~^^^^
TypeError: conversion from C to Decimal is not supported
```

## Appendix F. Манифест исполняемых блоков

Все hash ниже вычислены с полным конечным LF исходных локальных файлов. Полные блоки выше воспроизводят эти bytes после UTF-8 кодирования и добавления одного конечного LF.

| Файл | Bytes | LF | SHA256 |
|---|---:|---:|---|
| `certify_divisor.py` | 8994 | 214 | `578dcb6eb0705c93fe26c5668f960e9789fd276df0220055f62bba89adab52a8` |
| `certify60.stdout` | 1207 | 11 | `1ca45a858a318fc136089ebb613fc803748e138a0bc050609abebc8239db9013` |
| `certify90.stdout` | 1627 | 11 | `db2cc93b85553e3f11276fa1f65d44b062c12b5a1ff846bcfdc287a67541e0cf` |
| `diagnostic_diagonal.py` | 918 | 25 | `2da0aac3f828ba745919ebaf8d509346b16db032c55488017e33b29e3c39c091` |
| `diagnostic_diagonal.stdout` | 1022 | 15 | `7c15d38e6afbf6488f6ed987ea7614e68bffaebac18d31a89f426dd3252cd4e1` |
| `diagnostic_contour.py` | 856 | 23 | `a77b59f4d77521e4f2aeb8e5a4b94fc0500a682e7456c3d8e60e0a881f963dfc` |
| `diagnostic_contour.stdout` | 2493 | 35 | `4aca74e3c5747a4ae2d8ddc179f501afad971dd451f0ba57ea6f1db77928de0f` |
| `diagnostic_divisor_seed.py` | 919 | 25 | `1e98ad7a824a4dfca38541f085f6c108cc24eab4f613fc4b880065cc26ae8174` |
| `diagnostic_divisor_seed.stdout` | 1005 | 15 | `8dbd74c1b3be50890127ff7fbe8ecc640acfe8312a07ee244282d0e1d300c0a4` |
| `diagnostic_divisor_damped.py` | 1039 | 29 | `684571ccca28468e57b92dabd1512a0f5e4294f61fde985b6a6afa960b0daa2c` |
| `diagnostic_divisor_damped.stdout` | 763 | 10 | `d4244e47707759ce380b78db342e2250b3606514ad70cab506a971560ee51e1a` |
| `check_transport_and_constants.py` | 2659 | 55 | `1abd2563c2d41801b46c562a4f15d871a34a3886d57e56de267d9e231a0fc36e` |
| `check_transport_and_constants.stdout` | 991 | 11 | `a193fdcbe7faf99ca025147a72c00509d1b4cf6656799f352e8305369442d887` |
| `preregistration.txt` | 1347 | 19 | `a76d72c0e99c5a13a1b2a83095d753ec42d46199008d5394856af066a68f7afc` |
| `certify_divisor_transport_typeerror.py` | 8892 | 212 | `a033ea465322530b8fa50938c1b765a13a0e6234791f8dac7564c1eaeb5a1fb4` |
| `certify_typeerror.stdout` | 47 | 1 | `eaf80bef52cf120f0330d583f6cea9edfd39af7b9bf68e3a35bc174f718d18a0` |
| `certify_typeerror.stderr` | 497 | 10 | `47db0d483bcafcc7fc3e156e8093456fd4b66789c5c783d5718084dbfec8e23f` |

Конец полного отчёта. `KILL_NAMED_TWOCHANNEL_RF` относится только к фиксированной строгой относительной оценке. Положительность V, критерий Вейля и RH не объявлены установленными или опровергнутыми.
