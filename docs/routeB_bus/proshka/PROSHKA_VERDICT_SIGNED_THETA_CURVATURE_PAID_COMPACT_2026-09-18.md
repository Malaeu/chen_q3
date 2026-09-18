# STATUS: TRY_SIGNED_THETA_CURVATURE_WITH_PAID_COMPACT
```yaml
OPERATIVE_CLASS: TRY_SIGNED_THETA_CURVATURE_WITH_PAID_COMPACT
REQUEST_MODE: OWNER_DIRECT_RESEARCH_CONTINUATION
DATE: 2026-09-18
SOURCE_COMMIT: 181873396b93324681c7041972f2b68adbe1d672
PREVIOUS_VERDICT_COMMIT: 4dd6fe34401e1436144ef93b03548e780ee25507
EVIDENCE_STATE: PAPER_PROOF_WITH_EXECUTED_EXACT_INTEGER_INTERVAL_CHECKER
VERIFIER: PAPER
ARITHMETIC: OUTWARD_DYADIC_PYTHON_INTEGERS
PRECISION_BITS: 384
LAST_BLOCK_REPEAT_BITS: 768
INDEPENDENT_EXTERNAL_REVIEW: PENDING
LEAN_KERNEL_CHECKED: false
ARB_USED: false
ABSOLUTE_ENCLOSURE_REDERIVED: true
SIGNED_E_COH_CONTINUUM:
  scope: FINITE_CELL
  T: sqrt(20)
  sigma: (0,1/2]
  N: all_integers_at_least_5
COMPACT_FULL_H:
  scope: FINITE_CELL
  T: [-30,30]
  sigma: (0,1/2]
  lower_bound: sigma*exp(-pi*abs(T)/2)/25
GLOBAL_TAIL_ABOVE_30: OPEN
GLOBAL_E_COH_LOWER_BOUND: NOT_PROVED
GLOBAL_RELATIVE_MPLUS_BUDGET: NOT_PROVED
GLOBAL_QUARTER_MASS_GAP: NOT_PROVED
OLD_ONE_FIFTH_BUDGET:
  status: REFUTED
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: NEGATIVE_UPPER_ENVELOPE_ON_LITERAL_THETA_RAYS
  KILL_EVIDENCE_REF: section_2_and_exact_corner_certificate.json
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_FIXED_BUDGET
THETA_HEAD_NEGATIVE_WITNESS: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
LEAN_FILES_CHANGED: false
PRODUCTION_STATE_CHANGED: false
CODEX_DISPATCHED: false
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
REPRODUCER_DELIVERY: CHECKSUM_LOCKED_COMPANION_ARCHIVE_NOT_EMBEDDED
PRE_CLOSEOUT_TRANSPORT_REPAIR:
  earlier_commit: 5ec13116e3b266579d982d2c841a9ddfa2802460
  defect: corrupted_transcription_of_compressed_code_payload
  mathematical_statements_changed: false
  repair: remove_corrupted_payload_and_deliver_verified_archive
```

Ы. Получена нижняя оценка полного E_coh на целом горизонтальном отрезке для настоящих лучей. Затем получена нижняя оценка полной H на всём компактном прямоугольнике |T|<=30. Бесконечный хвост по T остаётся открытым. Это PAPER с выполненным целочисленным интервальным проверяющим кодом, не Lean и не Arb. Внешняя независимая приёмка ещё не выполнена.

## 1. Источники и точный объект

[ABSTRACT][PAPER] Прочитан действующий `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` на `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`.

Источник формул: `docs/routeB_bus/proshka/PROSHKA_FOLDED_FULL_SOURCE_CONTOUR_ENCLOSURE_2026-09-17.md`, §§1–6, на SOURCE_COMMIT, blob `796f1cb127b3b9d2caeff01e25d5c10f33a3fc61`. Предыдущий вердикт — `docs/routeB_bus/proshka/PROSHKA_VERDICT_COHERENT_MEANS_SIGN_TRANSFER_2026-09-18.md` на PREVIOUS_VERDICT_COMMIT. Его бюджет 1/5 проверяется, а не принимается как посылка.

Сохраняются буквальные определения

\[
a_n=\pi n^2,\quad
\phi_n(z)=(4a_n^2e^{9z/2}-6a_ne^{5z/2})e^{-a_ne^{2z}},\quad
\Phi=\sum_{n\ge1}\phi_n,
\]
\[
F(p)=\int_{\mathbb R}\Phi(t)e^{pt}dt=\xi(1/2+p),\qquad
\mathcal H(p)=4\Re(F'(p)\overline{F(p)}),
\]
\[
I_n(p,\theta)=\int_0^\infty\phi_n(t+i\theta)e^{p(t+i\theta)}dt,
\quad J_N=\sum_{n\le N}[I_n(p,\theta)+I_n(-p,-\theta)],
\quad h_N=4\Re(J_N'\overline{J_N}).
\]

Все p-производные берутся при фиксированных theta,N. Не дифференцируются theta(T) и округлённый срез. M_+ означает положительную спектральную часть всей матрицы головы, вычисленную на e=(1,...,1), не её собственное значение.

На компактных блоках ниже разрешён другой фиксированный вспомогательный срез. Не отождествляются разные головы или их спектральные массы: через абсолютную оболочку каждая оценивает одну и ту же полную F. Старые файлы, Lean и состояние маршрута не изменяются.

## 2. Настоящие лучи: старый бюджет убит, подписанный отрезок оплачен

[ABSTRACT][PAPER] Пусть X=sum I_n^+, Y=sum I_n^-, X_t=X'-i theta X, Y_t=i theta Y-Y'. При XY!=0 обозначим

\[
\alpha=X_t/X,\quad\beta=Y_t/Y,\quad m=(\Re\alpha+\Re\beta)/2.
\]

Точно:

\[
h_N/4=m(|X|^2-|Y|^2)+E_{\rm coh},
\]
\[
E_{\rm coh}=\frac{\Re\alpha-\Re\beta}{2}|X+Y|^2
-(\Im\alpha+\Im\beta)\Im(X\overline Y).
\tag{2.1}
\]

[FINITE_CELL][PAPER] При T=sqrt(20), theta=pi/4-1/(T+1), sigma=1/64,N=10 выполнен отрицательный верхний сертификат:

\[
-4.554\cdot10^{-7}<E_{\rm coh}+\tfrac15\sigma m|X|^2
<-4.193\cdot10^{-7}<0.
\tag{2.2}
\]

Одновременно h_N>0.00030972. Поэтому опровергнута только отдельная достаточная оценка epsilon=-E_coh/(sigma m|X|^2)<=1/5, не знак theta-головы. Точный интервал epsilon содержится в (0.20241049,0.20261750). Файл `exact_corner_certificate.json` содержит целые интервальные концы.

[FINITE_CELL][PAPER] На том же T и theta, для ВСЕХ N>=5 и ВСЕХ 0<sigma<=1/2 доказано:

\[
\boxed{-\frac{23}{10000}\sigma<E_{\rm coh}<-\frac{22}{10000}\sigma,}
\tag{2.3}
\]
\[
\boxed{m>\frac4{25},\qquad E_{\rm coh}\ge-\frac{51}{250}\sigma m|X|^2,\qquad
h_N\ge\frac{19}{1000}\sigma.}
\tag{2.4}
\]

Полученные наружные интервалы: E_coh/sigma в [-0.002256986,-0.002243842]; epsilon в [0.1717035,0.2037382]; m в [0.1627291,0.1628273]; h_N/sigma в [0.01982358,0.02006431]. Это весь горизонтальный отрезок, не точки. Константа 51/250 — ремонт ПОСЛЕ отказа 1/5, не предсказание задним числом.

### Почему сохраняется полный знак

[ABSTRACT][PAPER] При фиксированном T положим A(s)=exp(-i theta s)X(s+iT). Буквальное отражение лучей даёт

\[
Y(s)=e^{i\theta s}\overline{A(-s)},\quad
\alpha(s)=A'(s)/A(s),\quad\beta(s)=\overline{\alpha(-s)}.
\]

На безнулевой окрестности A определено чётное продолжение

\[
C(s)=\frac{\alpha(s)-\alpha(-s)}{2s}
=\frac1{2s}\int_{-s}^s(\log A)''(u)du.
\]

Для W=|X|^2+|Y|^2+2X conjugate(Y) формула (2.1) даёт

\[
\boxed{E_{\rm coh}/s=\Re(C(s)W(s)).}\tag{2.5}
\]

Действительно Re alpha-Re beta=2s Re C, Im alpha+Im beta=2s Im C, Re W=|X+Y|^2, Im W=2 Im(X conjugate(Y)). Сокращение при s=0 выполнено ДО оценки.

Для (2.3) вычислены первые пять лучей и оплачен весь хвост n>=6 на диске |z|<=3. На диске |z|<=2 доказано |A|>0.0835773 и |A'/A|<1.5108. Поэтому деление законно. Коэффициенты alpha вычисляются треугольным делением рядов; C берёт нечётные коэффициенты, m — чётные. Целое комплексное W сохраняется. Остатки Коши и интервальный Horner по s^2 в [0,1/4] дают (2.3)–(2.4). Все данные находятся в `axis_jets_exact.json`, `axis_certificate.json` и двух соответствующих исходниках.

## 3. Абсолютная оболочка повторно выведена без M_+

[ABSTRACT][PAPER] При c=cos(2theta)>0, M=N+1, pi cM^2>=1:

\[
D(c)=4c^{-4},\quad B(c,M)=448c^{-1}M^3e^{-\pi cM^2}.
\]

Для j=0,1,2 и |Re p|<=1/2:

\[
|F^{(j)}|,|J_N^{(j)}|\le De^{-\theta T},\qquad
|F^{(j)}-J_N^{(j)}|\le Be^{-\theta T}.
\tag{3.1}
\]

Подстановка u=exp(2t) сводит мажоранту пары к

\[
4a_n^2\int_1^\infty u^3e^{-a_ncu}du+
6a_n\int_1^\infty u^2e^{-a_ncu}du.
\]

Полная сумма <=36c^-4 pi^-2 sum n^-4<4c^-4. Для хвоста используются интегральные границы 16e^-b/b и 5e^-b/b, неравенство 64pi+30<256 и

\[
\sum_{n=M}^\infty n^2e^{-bn^2}
\le e^{-bM^2}\left(M^2+\frac M{2b}+\frac1{4b^2M}\right)
\le\frac74M^3e^{-bM^2}.
\]

Jacobi и контурная оценка исходника дают J_N(-conj(p))=conj(J_N(p)), H(iT)=h_N(iT)=0. При E_j=F^(j)-J_N^(j):

\[
F''\bar F-J_N''\bar J_N=E_2\bar F+J_N''\bar E_0.
\]

Отсюда и из разности квадратов первых производных

\[
|\partial_\sigma(H-h_N)|\le16DB e^{-2\theta T}.
\]

Интегрирование от нулевого начального значения доказывает

\[
\boxed{|H-h_N|\le\sigma e_N,\quad
 e_N=28672c^{-5}M^3e^{-\pi cM^2-2\theta T}.}\tag{3.2}
\]

Ни F, ни M_+ здесь не делители. Конечная сумма не объявляется чётной: сохраняется отражённая пара с оплаченным дефектом шва. Нормальная сходимость theta-ряда и сверхэкспоненциальная оценка на концах полосы |Im z|<pi/4 оправдывают контур и производные.

Для исходного r=0 среза

\[
\theta(T)=\pi/4-1/(T+1),\quad
M(T)=\left\lceil\sqrt{(T+1)(32+20\log(T+1))/3}\right\rceil
\]

сохраняется выведенное в §6 исходника следствие e_(N(T))<=exp(-pi T/2), T>=1. Используются c>=1/(T+1), exp(-2theta T)<=8exp(-pi T/2) и явный бюджет округления M. Это АБСОЛЮТНАЯ оценка, не относительная.

Повторная выкладка не равна внешней независимой приёмке новым автором. Последняя остаётся PENDING.

## 4. Доказательство положительности полной H на континууме

[FINITE_CELL][PAPER] Получено

\[
\boxed{H(\sigma+iT)\ge\frac1{25}\sigma e^{-\pi|T|/2}>0
\quad(0<\sigma\le1/2,\ |T|\le30).}\tag{4.1}
\]

На 4<=|T|<=30 усиление:

\[
\boxed{H(\sigma+iT)\ge10\sigma e^{-\pi|T|/2}.}\tag{4.2}
\]

Не используются старый q>18, список нулей, простота нулей, RH, G>=1/4 или относительный пол M_+.

### 4.1 Аналитические коэффициенты и оплаченные остатки

Центры t_j=1,3,...,29 покрывают замкнутыми блоками [t_j-1,t_j+1] весь [0,30]. На блоке фиксированы theta_j=pi/4-1/(t_j+1), N_j из (6.3) В ЦЕНТРЕ. Пусть

\[
A_j(z)=e^{\theta_jt_j-i\theta_jz}\sum_{n\le N_j}I_n(it_j+z,\theta_j),\quad
P_j(z)=A_j(z)+\overline{A_j(-\bar z)}.
\]

A_j есть интеграл sum phi_n(t+i theta_j) exp(it_j t) exp(zt). Мажоранта §3 даёт |A_j|<=D_j на |z|<=3; чистые t-моменты порядков 0,1,2 также <=D_j при |Re z|<=1/2. Здесь достаточно |Re z|+j<=7/2.

Для z=sigma+i(T-t_j):

\[
h_{N_j}=4e^{-2\theta_jT}\Re(P_j'(z)\overline{P_j(z)}).
\]

Из 64 значений на единичной окружности получаются Taylor-коэффициенты a_k до k=32. Их дополнительная ошибка Коши точно ограничена:

\[
\left|a_k-\frac1{64}\sum_{l=0}^{63}A_j(\omega_l)\omega_l^{-k}\right|
\le\frac{D_j3^{-k}}{3^{64}-1},\quad\omega_l=e^{2\pi il/64}.
\tag{4.3}
\]

Это оценка суммарного вклада a_(k+64q), q>=1. Эти узлы НЕ являются сеткой, из которой делается вывод о знаке между точками.

Берутся точные dyadic-середины коэффициентов. Радиусы идут в бюджеты eta_0,eta_1,eta_2. Для r=sqrt(5)/2, q=r/3, m_0=33 хвост P и его производных ограничен

\[
e_0=2D_jq^{m_0}/(1-q),\quad
e_1=(2D_j/3)q^{m_0-1}(m_0-(m_0-1)q)/(1-q)^2,
\]
\[
e_2=(2D_j/9)q^{m_0-2}
[m_0(m_0-1)/(1-q)+2m_0q/(1-q)^2+2q^2/(1-q)^3].
\]

Добавление 2 sum radius(a_k) r^k и производных даёт eta_j. И точный, и полиномиальный HB-числители равны нулю на sigma=0. Поэтому после интегрирования их производной ошибка h_N/sigma ограничена

\[
B_{\rm jet}=4[2D_j\eta_2+(2D_j+\eta_2)\eta_0+(4D_j+\eta_1)\eta_1].
\tag{4.4}
\]

### 4.2 Полиномиальная нижняя оболочка

Для полинома из середин P_32 функция psi(w)=P_32(iw) имеет вещественные коэффициенты. Значит

\[
R_j(\sigma^2,t)=\frac2\sigma\partial_\sigma|\psi(t+i\sigma)|^2
\]

есть полином степени <=31 по sigma^2 и <=62 по t=T-t_j. Он точно представляет 4Re(P_32' conjugate(P_32))/sigma. Чётность по sigma убирает деление и при sigma=0.

Перевод в тензорный базис Бернштейна степени (31,62) на [0,1/4] x [-1,1] даёт 2016 коэффициентов. Базисные функции неотрицательны и в сумме равны 1. Поэтому минимум нижних концов коэффициентов оценивает ВЕСЬ полином на ВЕСЬ прямоугольник.

Окончательный нижний бюджет:

\[
\boxed{\frac H{\sigma e^{-2\theta_jT}}
\ge\min b_{kl}-B_{\rm jet}-16D_jB(c_j,N_j+1)=L_j.}\tag{4.5}
\]

И коэффициентный, и theta-хвост уже ВЫЧТЕНЫ.

| Замкнутый блок T | N_j | Рациональная нижняя граница: L_j > |
|---|---:|---:|
| [0,2] | 5 | 0.045 |
| [2,4] | 8 | 0.329 |
| [4,6] | 11 | 3.31 |
| [6,8] | 14 | 27.81 |
| [8,10] | 16 | 173.95 |
| [10,12] | 18 | 767.71 |
| [12,14] | 19 | 2358.31 |
| [14,16] | 21 | 5520.33 |
| [16,18] | 23 | 12483.51 |
| [18,20] | 24 | 27073.25 |
| [20,22] | 26 | 40296.00 |
| [22,24] | 27 | 47814.31 |
| [24,26] | 29 | 78689.96 |
| [26,28] | 30 | 169598.03 |
| [28,30] | 31 | 206050.5 |

Все границы проверены как рациональные сравнения с целыми концами сертификатов. Все L_j>1/25; exp(-2theta_j T)>=exp(-pi T/2) доказывает (4.1). При t_j>=5 имеем L_j>3 и exp(2T/(t_j+1))>=exp(4/3)>10/3, что даёт (4.2).

Все стыки и края включены. Sigma=0 обрабатывается аналитически до оценки. Отрицательные T покрывает реальность F. Никакой дифференциальной склейки разных N не нужно: склеиваются нижние оценки одной H.

Последний блок повторён при 768 битах: L_29>206090.8. Его B_jet падает с <47.36 до <7.051; оба бюджета положительны. Остальные 14 блоков не заявляются повторёнными при 768 битах.

## 5. Арифметика и проверки

[ABSTRACT][PAPER] Проверяющий код использует Python integers, наружное округление на 2^-P, integer sqrt, рациональные Taylor-суммы с хвостами. Decimal — только отображение. Mpmath не производит сертификатные границы.

Exp редуцируется до |x|<=1/8 и 64 членов с остатком <=2|x|^65/65!. Sin/cos используют 48 членов с остатком <=2|x|^96/96!. Log и atan используют сходящиеся ряды с геометрическим хвостом. Pi — 16atan(1/5)-4atan(1/239).

Gamma использует сдвиг 32 и Stirling с B_46; остаток логарифма ограничен |B_48|/[48*47*(Re(z+32))^47] из интеграла Euler–Maclaurin. Обратный сдвиг — точная рекурсия.

Для n<=5 применяется сходящийся ряд

\[
\Gamma(a,z)=\Gamma(a)-z^a\sum_{k\ge0}\frac{(-z)^k}{k!(a+k)}
\]

до 320 включительно, с хвостом <=R^321/[321!(Re a+321)(1-R/322)], R=|z|<322.

Для n>=6 применяется горизонтальный интеграл и его Taylor-остаток:

\[
\Gamma(a,z)=z^{a-1}e^{-z}
\left[\sum_{k<64}(a-1)_{\underline k}z^{-k}+R_{64}\right],
\quad |R_{64}|\le |(a-1)_{\underline{64}}||z|^{-64}e^{|\Im a|\pi/2}.
\]

Условия: Re z>0 и Re a-65<=0. В Taylor-остатке |1+ut/z|>=1, |arg(1+ut/z)|<=pi/2; интеграл exp(-t)t^64/64! равен 1. Это явный остаток, не предположение о точности асимптотики.

Определения и рекурсии сверены с NIST DLMF §§8.2,8.7,8.8; Jacobi — §20.7; Stirling — §5.11. Полные выкладки и исходники находятся в сопровождающем архиве.

Выполнены 300 рациональных тестов примитивов, шесть Gamma(1,z)=exp(-z) контролей и Gamma-рекурсия. Plant psi(w)=1+w^2 даёт h/sigma=8(t^2-1+sigma^2); отрицательное направление обнаруживается. Положительный plant psi(w)=w даёт 4. Отдельный 1/5-plant на настоящих лучах отвергнут по ВЕРХНЕЙ границе. Десять сверок с прямой xi/zeta выполнены как диагностика, не доказательство.

Два отказа представления до результата сохранены в отчёте. Обратный огромный factorial чрезмерно расширял безопасные интервалы; заменён прямым целочисленным делением. Прямая смена базиса интервальных коэффициентов давала бесполезную отрицательную НИЖНЮЮ оценку; это не контрпример. Ремонт — точные середины и оплаченный eta-бюджет. Ни блоки, ни степень 32 не менялись; разрешённая резервная степень 48 не потребовалась.

## 6. Что это даёт исходному срезу и чего не даёт

[FINITE_CELL][PAPER] Для исходных theta(T),N(T) из (6.3), r=0, сочетание (4.2) и e_(N(T))<=exp(-pi T/2) даёт

\[
\boxed{h_{N(T)}\ge9\sigma e^{-\pi T/2}\quad(4\le T\le30).}\tag{6.1}
\]

Это прямой знак исходной адаптивной головы. Он не является доказательством G>=1/4 или глобального относительного e_N<M_+/4. Компакт закрыт прямым вычитанием абсолютного остатка из полной нижней оценки.

[COFINAL_FAMILY][CONDITIONAL] T>30 остаётся открытым. Для него здесь нет глобальной оценки E_coh, положительности H или относительного M_+-бюджета. RH не заявлена.

[ABSTRACT][PAPER] Потребителю достаточно H>=0 на всей области. Тогда |F(sigma+iT)|^2 не убывает по sigma. Внеосевой нуль заставил бы F обращаться в ноль на горизонтальном отрезке; теорема тождественности запрещает это. Чётность переносит исключение на левую половину полосы. Значит строгий единый относительный пол — достаточный, но не обязательный интерфейс.

Другой достаточный интерфейс: в каждой фиксированной точке доказать h_(N_k)>=0 при N_k->infinity и фиксированном theta. Абсолютный хвост стремится к нулю и даёт H>=0. Это новое обязательство по N, не вывод из знака единственного N(T).

## 7. Predictions, dependency epistemics и одна директива

[ABSTRACT][PAPER] До соответствующих тестов зарегистрированы: P_ABSOLUTE_REVIEW p=.94; P_JOINT_NOT_SEPARATE p=.65; P_REFLECTION_FACTOR p=.97; P_COMPACT_SIGNED_JET p=.80; P_LOW_SOURCE_BLOCKS p=.97. Все CONFIRMED в зарегистрированных областях. Отдельный старый бюджет 1/5 REFUTED. Новый 51/250 не выдаётся за прежнее предсказание. Регистрация сохранена в `registration.json`.

Два кандидата для остатка выше 30:

R1: подписанное Re(CW), отражённая логарифмическая кривизна настоящей гамма-суммы. Kill-power 9/10, аналитическая стоимость 7/10. Требуется оценка совместной фазы, не только средних. При нулях кластеров нужен безделительный вид.

R2: полный безделительный h_N/sigma с абсолютным хвостом либо неотрицательная кофинальная подпоследовательность голов. Kill-power 10/10, глобальная стоимость 8/10. Конечное покрытие не переносится на бесконечность без нового источникового доказательства. Эти оценки стоимости — ориентиры выбора, не вероятности доказательства.

DISCRIMINATOR: подписанный полный h_N/sigma-e_N или бюджет (4.5). Нижний конец >=0 даёт PASS на заявленной области. Отрицательный верхний конец полной H/sigma даёт отрицательный свидетель. Интервал через ноль остаётся INCONCLUSIVE. Отрицательный верхний конец отдельной достаточной оценки убивает только её.

[COFINAL_FAMILY][CONDITIONAL]
DOWNSTREAM_CONSUMER: исключение внеосевых нулей полной F.
ACTUAL_CONSUMER_REQUIREMENT: H>=0 для всех 0<sigma<=1/2,T; F entire, even, nonzero.
ORIGINAL_REQUESTED_OBJECT: глобальный E_coh-бюджет и e_N<M_+/4.
ORIGINAL_OBJECT_IS: NOT_NECESSARY как единственная форма доказательства.
KNOWN_WEAKER_INTERFACES: прямое H>=0; h_N/sigma>=e_N; неотрицательные кофинальные головы плюс абсолютная сходимость.
FAILURE_TYPE: NO_DERIVATION для T>30; COUNTEREXAMPLE только для 1/5.
EPISTEMIC_STATUS: RESEARCH_DEBT для глобального хвоста; MATHEMATICALLY_DEAD для конкретного 1/5.
NOVELTY_AXIS: сохранение подписанной комплексной кривизны и полиномиальная сертификация полной H/sigma.
REOPEN_TRIGGER: источник-специфическая нижняя граница полного выражения при T>30 или отрицательная верхняя граница того же объекта. Новая сетка средних не подходит.

Единственная следующая локальная директива: независимо проверить остатки §5 и воспроизвести сертификаты из пустого каталога. Не расширять T, не подгонять константы, не менять production state и не делать RH-export. Успех — все 15 покрытий, осевой сертификат и отрицательный plant проходят. Отказ — точное первое несовпавшее тождество, остаток или целый интервал. Codex не запускался.

Closeout: компакт |T|<=30 и весь горизонтальный E_coh-отрезок оплачены на уровне PAPER/checker. Убит только 1/5. Запрещённые повторы: знак из средних; контроль числителя из близости масс; контрпример из отрицательной нижней границы; глобализация конечных клеток. Минимальный остаток: SOURCE_SIGNED_FULL_H_FOR_T_ABOVE_30. Memory: reflection removes sigma before bounds; exact midpoint polynomial preserves cancellation; absolute enclosure can pay compact source positivity without a relative mass floor.

## 8. Проверяемая доставка и handoff

[FINITE_CELL][PAPER] Полные исходники, целые сертификаты, логи, регистрация и `ANALYTIC_APPENDIX.md` поставлены отдельным архивом в ответе владельцу:

`theta_signed_coherence_compact_2026_09_18.zip`

SHA-256: `d737474c1ed3220e779d9f23454ae473184afa2cf78c29843a9f2859e97bd96f`.

Архив НЕ объявляется сохранённым в GitHub. В GitHub записан этот единственный verdict. Первоначальный встроенный compressed payload на коммите 5ec13116... повредился при транскрипции; он удалён до closeout. Математические результаты и проверенные локальные исходники не менялись. Для воспроизведения нужен указанный архив, а не повреждённая историческая версия документа.

В архиве `SHA256SUMS.json` фиксирует точные хеши каждого исходника и сертификата. Основные программы: `exact_dyadic.py`, `check_exact_corner.py`, `build_axis_jets.py`, `certify_axis.py`, `compact_certificate.py`, `self_tests.py`. Они используют Python standard library. `validate_all.py` и `check_rays.py` дополнительно используют mpmath только для необязательной диагностики.

WORKDIR: каталог распакованного архива, содержащий эти исходники. Для независимого пересчёта скопировать только шесть основных .py в новый пустой каталог; не переносить кэш jets.

```bash
python3 check_exact_corner.py
python3 build_axis_jets.py
python3 certify_axis.py
for c in 1 3 5 7 9 11 13 15 17 19 21 23 25 27 29; do
  python3 compact_certificate.py "$c"
done
DYADIC_BITS=768 python3 compact_certificate.py 29
python3 self_tests.py
python3 - <<'PY'
import json
from fractions import Fraction
from pathlib import Path
for c in range(1,30,2):
    r=json.loads(Path(f'compact_certificate_T{c}_K32.json').read_text())
    L=Fraction(r['integer_paid_lower'],r['denominator'])
    assert r['domain']=={'sigma':['0','1/2'],'T':[c-1,c+1]}
    assert L>Fraction(1,25)
    if c>=5: assert L>3
assert json.loads(Path('exact_corner_certificate.json').read_text())['old_budget_negative']
a=json.loads(Path('axis_certificate.json').read_text())
assert a['E_ge_minus_51_over_250_sigma_m_X2']
assert a['signed_E_bounds_minus23_minus22_over10000']
r=json.loads(Path('compact_certificate_T29_K32_P768.json').read_text())
assert Fraction(r['integer_paid_lower'],r['denominator'])>3
print('EXACT_COMPACT_AND_SIGNED_COHERENCE_CHECKS_PASS')
PY
```

Переменная c — центр блока: c=5 означает весь T в [4,6]. DYADIC_BITS — число битов знаменателя 2^P. Это не число точек сетки. Исходники используют кэш только при его наличии, поэтому независимый пересчёт проводится в пустом каталоге.

Lean-файлов нет; Lean gate и axiom profile неприменимы. Внешняя приёмка может подтвердить или опровергнуть PAPER/checker результат, но не закрывает автоматически глобальный хвост и не делает RH-claim.
