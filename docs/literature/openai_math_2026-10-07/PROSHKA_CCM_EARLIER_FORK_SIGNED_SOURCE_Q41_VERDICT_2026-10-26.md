# STATUS: TRY_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41
```yaml
OPERATIVE_CLASS: TRY_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41
REQUEST_ID: Q41_EARLIER_FORK_SIGNED_SOURCE
DATE: '2026-10-26'
VERDICT_CODE: NO_NEW_SIGNED_INPUT_FINITE_SHORT_INVERSE_PREFLIGHT_ONLY
REQUEST_COMPLETION: PARTIAL_NO_NEW_ARITHMETIC_INEQUALITY
PROGRESS_CLASS: NO_PROGRESS
PRIMARY_CONSUMER: OPEN
RH: OPEN_NOT_CLAIMED
CF22_PYSR: PARKED_REOPENABLE
SOURCE: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
REQUEST_BYTES: 208316
REQUEST_LF: 3423
REQUEST_SHA256: b311d750de7cca08c919dc77d1665f40a49255914f094b74bf629e9ca6a7b086
BASE_COMMIT: 26fa7ca66ffc1c2c03655fc5eea32017fe80a7d8
SOURCE_BODIES: 10
MANIFEST: ALL_BYTE_LF_SHA256_FRAMES_MATCH
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
CHOSEN_FORK: Q32_COMPLETE_FINITE_CENTRAL_PAIRING_BEFORE_SEPARATE_SIZES
ATTEMPT: FINITE_REPEATED_SHORT_MOBIUS_INVERSION_INSIDE_THE_SAME_PAIRING
NEW_FAVOURABLE_INEQUALITY: NOT_OBTAINED
NEW_ARITHMETIC_SUBLEMMA_REDUCING_CONSUMER_DEBT: NOT_OBTAINED
KILL_SCOPE: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
CLOSES: []
OPENS: []
REPOSITORY_WRITES: false
HISTORICAL_CODE_EXECUTED: false
NEW_INDEPENDENT_AUDIT: false
LEAN: NOT_RUN
ARB_INTERVAL: NOT_RUN
PRODUCTION_SPECTRA: NOT_RUN
```

# Q41. Ранний возврат: проверка короткого обращения, без нового знакового поставщика

## 0. Ответ по существу и граница выполнения

**Независимую одностороннюю оценку, запрошенную в Q41, я не получил. Не получил и новую арифметическую подлемму, которая уменьшает её неоплаченный показатель. Эта содержательная часть поручения остаётся невыполненной.**

Выполнены полное чтение и проверка десяти источников, выбор документированной ранней развилки, один конечный коэффициентный preflight и точный возврат к исходному потребителю. Проверенный кандидат — многократное короткое обращение Мёбиуса внутри полной центральной формы Q32. Оно перемешивает знаковые каналы до модулей, но доказанная часть оказалась **только точным разложением**. Ни короткость отдельных множителей, ни исчезновение конечного свёрточного остатка не дали знака оставшейся формы.

Поэтому ниже **нет** нового дорогого norm certificate, построенного ради очередного half-power no-go. Нет также утверждения, что рассмотренное разложение бесполезно при любом дальнейшем аргументе. Его применение в этой попытке остановлено на первой недоказанной арифметической строке.

Сохранён лучший приложенный безусловный бюджет
\[
 s_{\rm keep}\le 6\sqrt m+6m^{1/4}.
\]
Ни меньшая полная степень, ни положительный коэффициентный запас на настоящей нулеселективной паре не заявляются. Тождество и тесты из этого файла **не считаются доказательственным прогрессом**.

### Что здесь является входом, а что — собственной работой

- **Входы из пакета:** исходный оператор и контакты; полная карта Q32; краткий/архимедов возвраты; сохранённый верх; условный sparse-band receiver. Их принятые PAPER-статусы используются в заявленной области, не повышаются до формальной проверки.
- **Собственный расчёт:** конечное короткое обращение с точным остатком, его вложение в целую центральную форму и причинный оператор, проверка коэффициентов на простых и составных, полный список расходов этой карты.
- **Не получено:** первое дополнительное неравенство, использующее совместную связь actual \(\Lambda-1\) с достижимым тестом, а не одну лишь алгебру коэффициентов.

Само конечное обращение не заявляется ни новым тождеством в теории чисел, ни новым независимым поставщиком. Внешняя оценочная теорема для него **не импортирована**.

## 1. Intake и действующее поручение

Канонический файл:

```text
PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_2026-10-26.txt
208316 bytes
3423 LF
SHA256 b311d750de7cca08c919dc77d1665f40a49255914f094b74bf629e9ca6a7b086
```

Размер и общий хеш **измерены по прикреплённым байтам**; в короткой пользовательской подписи они не были заданы. Все десять внутренних frames проверены отдельно: имя, число байтов, LF, SHA-256 и точная граница тела. Один separator LF не включён в тело. Полный manifest приведён в §10 и в машиночитаемом приложении.

Прочитаны все тела, включая полный S2, полный S6 и их исторический код. **Исторические команды и код не исполнялись.** Проверка хеша устанавливает тождественность текста, а не правильность его математических утверждений.

Bootstrap прочитан через GitHub connector с ветки `rh_clean`: `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Другие живые репозиторные файлы для выбора задания не сканировались. Репозиторий не изменялся.

### Сверка с уже закрытыми входами

| Источник | Что учитывается в Q41 | Чего из него не следует |
|---|---|---|
| S1–S2, Q40 | Реальная iso/rest-компенсация на одной возвращённой семье; точный оптимум incidence-перераспределения | Равномерная оценка на всех \(c=Pc\) |
| S3, Cotlar | Диагональный/subset расход мешает указанным декомпозициям | Невозможность signed-сравнения исходного оператора |
| S4 | Полное центрирование и уже проверенная недостаточная PNT-цена | Новый subpower-вход из повторного Abel/PNT |
| S5–S6 | Полная конечная центральная форма и \(O_\epsilon(m^{2\epsilon})\)-возврат | Знак центральной формы |
| S7 | Оплаченный неквадратсвободный сектор; \(A+C_{\rm sf}=U_{\rm sf}\) | Lower \(C_{\rm sf}\) после удаления простых |
| S8 | Точные ограничения резольвентного переноса и нормировки пары | Благоприятная оценка из adverse selected-zero identity |
| S9 | Полилогарифмический свидетель и оплаченная аналитическая часть контура | Знак совместных вычетов |
| S10 | Условный receiver на исходной фиксированной sparse band | Независимый арифметический верх |

В этой попытке не повторяются Cotlar, отдельные HS-цены, положительные части компонент, независимые фазы, перенастройка Q32-cutoff, log-chord или положительность произвольного Gram. Многократное короткое обращение меняет алгебраические каналы, но **не считается новым арифметическим методом только потому, что каналов стало больше**. Это принципиальная граница данной проверки.

## 2. Исходный объект и оплаченная ранняя развилка

**[COFINAL_FAMILY | PAPER, inherited S5–S6,S10]** Фиксируем сначала
\[
 0<\epsilon<1/32,
 \qquad L=\log m,
 \qquad M=R=\lfloor m^\epsilon\rfloor,
 \qquad \Omega=2\pi M/L.
\]
Все последующие константы могут зависеть от этого фиксированного \(\epsilon\), но не от \(m\) или худшего вектора. Производственная матрица по-прежнему имеет \(N=m\).

Пусть \(F_M\) — исходный изометрический Fourier-синтез на \([0,L]\), а \(P\) — исходный проектор на три контакта. Для \(c=Pc\), \(f=F_Mc\), сохраняются
\[
 \|f\|_2=\|c\|_2,
 \qquad f(0)=f(L)=0,
 \qquad \int_0^L e^{\pm t/2}f(t)\,dt=0.
\]
Используется нулевое продолжение физической функции, не периодическая подмена сдвигов.

Запишем
\[
 h(x)=x^{-1/2}P Q_M(\log x)P,
 \quad A=\sum_{n\le m}\Lambda(n)h(n),
 \quad C^0=A+H_d,
 \quad 0\preceq H_d\preceq4P.
 \tag{2.1}
\]
Полный непрерывный член уже возвращён:
\[
 \int_1^m h(x)\,dx=-H_d.
 \tag{2.2}
\]
Это известный вход, не результат Q41.

### 2.1. Центральная форма, которую здесь не переоцениваем отдельно

Используем буквальные оболочки S5–S6. Пусть
\[
 B=\max(4,\lceil m^{2\epsilon}\rceil),\qquad X_\ell=2^\ell B,
\]
\(\chi_\ell\) — уже выбранное гладкое разбиение, \(I_\ell=[X_\ell,4X_\ell]\cap[1,m]\cap\mathbb Z\),
\[
 a_\ell(n)=\chi_\ell(n)h(n),
 \qquad b_\ell(n)=(\Lambda(n)-1)\mathbf1_{I_\ell}(n),
 \qquad \lambda_\ell=X_\ell^{-5/8}.
\]
Cutoff стоит **один раз**, на тестовой стороне. Он не дублируется в \(b_\ell\).

С \(e(t)=e^{2\pi it}\) исходная центральная форма равна
\[
 N_\star=\sum_\ell\int_{|t|<\lambda_\ell}
              \widehat b_\ell(t)\widehat a_\ell(-t)\,dt.
 \tag{2.3}
\]
Карта возврата уже доказана в S6 §4.6:
\[
 \boxed{A=N_\star+E_\star,\qquad
 \|E_\star\|\le r_\star\le C_\epsilon m^{2\epsilon}.}
 \tag{2.4}
\]
В \(E_\star\) входят весь исходный нижний участок, постоянная модель, обе частотные внешние области и все terminal/shell-overlap расходы. **Ни одна из этих оценок здесь не предъявляется повторно как выигрыш.**

Для буквального конечного возврата удобно обозначить
\[
 k_\lambda(d)=
 \begin{cases}2\lambda,&d=0,\\
 \sin(2\pi\lambda d)/(\pi d),&d\ne0,
 \end{cases}
\]
\[
 \widetilde a_\ell(n)=
       \sum_{v\in I_\ell}a_\ell(v)k_{\lambda_\ell}(v-n).
\]
Тогда конечное раскрытие (2.3) даёт
\[
 N_\star=
 \sum_\ell\sum_{n\in I_\ell}(\Lambda(n)-1)\widetilde a_\ell(n).
 \tag{2.5}
\]
Это контрольное равенство: перемены порядка допустимы для конечных сумм. Оно **не** новая арифметическая оценка.

Важный край: \(h(m)=0\) не влечёт \(\widetilde a_\ell(m)=0\). Поэтому каждый арифметический коэффициент при \(n=m\) ниже сохраняется. Его полное сопряжение с дополнением уже входит в (2.4).

## 3. Один выбранный preflight: конечное короткое обращение Мёбиуса

### 3.1. Проверяемое предложение и его риск

Идея — не отделять положительные isolated-блоки от отрицательного rest. Вместо этого в (2.5) раскрыть **один и тот же** коэффициент \(\Lambda(n)\) через несколько коротких мёбиусовых переменных. Таким образом, знаковые каналы пересекаются на одном полном произведении \(n\), с одним и тем же \(\widetilde a_\ell(n)\).

Точное предварительное требование к полезности: после такого раскрытия надо доказать неравенство для целой чередующейся суммы, которого не было до раскрытия. Короткость отдельных переменных сама по себе этим неравенством не является.

Ниже полностью проверяется алгебраический вход. Уже на нём видно, что автоматического малого коэффициента у больших простых не появляется. **Это не опровержение дальнейшего совместного multilinear-сравнения; такого сравнения в данной работе не удалось получить.**

### 3.2. Конечная свёрточная алгебра

**[ABSTRACT | PAPER]** Для целого \(m\) работаем с функциями на \(1\le n\le m\), с обычной усечённой свёрткой Дирихле
\[
 (a*b)(n)=\sum_{d\mid n}a(d)b(n/d),\qquad n\le m.
\]
Усечение сохраняет ассоциативность: член с индексом \(>m\) не может участвовать в произведении с результатом \(\le m\). Никакой бесконечный ряд или контур не вводится.

Различаем единицу алгебры \(\mathbf e(n)=\mathbf1_{n=1}\) и постоянную арифметическую функцию \(\mathbf1(n)=1\). Положим
\[
 \ell(n)=\log n,
 \qquad u_U(n)=\mu(n)\mathbf1_{n\le U},
 \qquad y_U=\mathbf e-\mathbf1*u_U,
 \qquad 1\le U\le m.
 \tag{3.1}
\]
Из разложения по простым
\[
 \sum_{d\mid n}\mu(d)=\prod_{p\mid n}(1-1)=0\quad(n>1)
\]
и \(\mu(1)=1\) следует
\[
 y_U(n)=0\quad(1\le n\le U).
 \tag{3.2}
\]
Следовательно,
\[
 \operatorname{supp}(y_U^{*K})\subseteq[(U+1)^K,m].
 \tag{3.3}
\]
Это свойство **настоящих** коэффициентов Мёбиуса, не случайных меток. Оно является точной поддержкой, а не оценкой signed-формы.

Полная \(\mu\) является обратной к \(\mathbf1\) в этой конечной алгебре. Геометрическая формула даёт
\[
 \mu=u_U*\sum_{r=0}^{K-1}y_U^{*r}+\mu*y_U^{*K}.
 \tag{3.4}
\]
Раскрывая полином \(\sum_{r=0}^{K-1}(1-x)^r\), получаем
\[
 \boxed{
 \mu=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj
 u_U^{*j}*\mathbf1^{*(j-1)}
 +\mu*y_U^{*K}.
 }
 \tag{3.5}
\]
Например, коэффициент при \(x^{j-1}\) равен
\( (-1)^{j-1}\sum_{r=j-1}^{K-1}\binom r{j-1}=(-1)^{j-1}\binom Kj\), что проверяет знак и биномиальный множитель.

Умножаем (3.5) на \(\ell\), используя полное \(\mu*\ell=\Lambda\):
\[
 \boxed{
 \Lambda=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj Q_{j,U}
 +\Lambda*y_U^{*K},
 \qquad
 Q_{j,U}=u_U^{*j}*\mathbf1^{*(j-1)}*\ell.
 }
 \tag{3.6}
\]
Первое тождество \(\mu*\ell=\Lambda\) следует, например, из
\(\mathbf1*\Lambda=\ell\) с полным сохранением степеней простых. Для \(p^a\) сумма делителей \(\Lambda\) даёт \(a\log p\), а при умножении различных простых складываются их логарифмы.

**Остаток (3.6) нельзя удалить без проверки поддержки.** При \(U=2,K=3,m=64\) коэффициент \(\log2\) в \((\Lambda*y_U^{*K})(54)\) равен \(-1\). Этот случай включён в exact controls.

### 3.3. Единственный фиксированный производственный выбор

Берём
\[
 U=R=\lfloor m^\epsilon\rfloor,
 \qquad K=\lceil1/\epsilon\rceil.
 \tag{3.7}
\]
\(K\) фиксируется после \(\epsilon\), **до** роста \(m\). Поскольку
\[
 U+1>m^\epsilon,\qquad
 (U+1)^K>m^{\epsilon K}\ge m,
\]
остаток в (3.6) равен нулю на всём \(1\le n\le m\), включая верхнюю точку. Поэтому
\[
 \boxed{
 \Lambda(n)=\sum_{j=1}^K(-1)^{j-1}\binom Kj Q_{j,U}(n)
 \quad(1\le n\le m).
 }
 \tag{3.8}
\]
В развёрнутом виде
\[
 Q_{j,U}(n)=
 \sum_{\substack{d_1\cdots d_j a_1\cdots a_j=n\\d_i\le U}}
 \mu(d_1)\cdots\mu(d_j)\log a_j.
 \tag{3.9}
\]
Все переменные положительные целые. Переставляемые \(d_i,a_i\) считаются **упорядоченно**; общий гиперболический cutoff остаётся буквальным. Малость каждого \(d_i\) не ограничивает \(a_j\) величиной \(U\).

## 4. Полный signed return: никакой новой нормы или проектора

### 4.1. Вложение непосредственно в центральную форму

**[ABSTRACT | PAPER]** Определим целые матрицы
\[
 \mathcal B_j=
 \sum_\ell\sum_{n\in I_\ell}Q_{j,U}(n)\widetilde a_\ell(n),
 \qquad
 \mathcal D_1=
 \sum_\ell\sum_{n\in I_\ell}\widetilde a_\ell(n).
 \tag{4.1}
\]
Из (2.5),(3.8) получается
\[
 \boxed{
 N_\star=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj\mathcal B_j-\mathcal D_1.
 }
 \tag{4.2}
\]
Это равенство матриц на **том же** \(\operatorname{ran}P\), не усреднение по новому пространству. Оно одновременно верно для любого комплексного \(c=Pc\) и для всех \(W=PWP\succeq0\). При \(\operatorname{Tr}W=1\) контрактируем всю правую часть одним и тем же \(W\).

В частности,
\[
 \operatorname{Tr}(WN_\star)=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj
 \operatorname{Tr}(W\mathcal B_j)-\operatorname{Tr}(W\mathcal D_1).
 \tag{4.3}
\]
Ни модуль по \(j\), ни Cauchy по \(d_i\), ни отдельная норма арифметического Fourier-полинома здесь не взяты. Постоянный дискретный член \(-1\) сохранён в \(\mathcal D_1\); в полной исходной локализации атом \(n=1\) также остаётся в уже оплаченном нижнем возврате S5–S6.

Ошибка **самой** карты (4.2) равна нулю. Общая цена возвращения к \(A\) остаётся ровно прежней \(r_\star\), а не \(2^K r_\star\): мы не применяем Q32-возврат отдельно к каждому искусственному каналу.

### 4.2. Контроль через причинные сдвиги

Чтобы исключить скрытую замену носителя, введём на исходном физическом \(L^2(0,L)\)
\[
 (V_sf)(t)=\mathbf1_{s\le t\le L}f(t-s),
 \qquad V_sV_t=V_{s+t},\quad V_s=0\ (s\ge L).
\]
Для конечной арифметической функции \(a\) положим
\[
 \mathcal E_\sigma(a)=\sum_{n\le m}a(n)n^{-\sigma}V_{\log n}.
 \tag{4.4}
\]
Это точный гомоморфизм конечной свёрточной алгебры:
\[
 \mathcal E_\sigma(a*b)=\mathcal E_\sigma(a)\mathcal E_\sigma(b).
\]
Индекс \(n=m\) сохраняется формально, а его физический сдвиг равен нулю. Индексы \(>m\) не дают скрытого хвоста: соответствующие сдвиги также нулевые. Это не означает, что арифметические коэффициенты там равны нулю вне нашей конечной алгебры.

С обозначениями
\[
 Z_\sigma=\mathcal E_\sigma(\mathbf1),\quad
 M_{U,\sigma}=\mathcal E_\sigma(u_U),\quad
 J_\sigma=\mathcal E_\sigma(\ell)
\]
получается
\[
 \mathcal E_{1/2}(\Lambda)=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj
 M_{U,1/2}^{\,j}Z_{1/2}^{\,j-1}J_{1/2}.
 \tag{4.5}
\]
Только **после всех произведений** прибавляется adjoint и выполняется сжатие:
\[
 A=PF_M^*\left[\mathcal E_{1/2}(\Lambda)
                      +\mathcal E_{1/2}(\Lambda)^*\right]F_MP.
 \tag{4.6}
\]
Промежуточный \(P\) нигде не вставлен. Не утверждается, что каждый причинный множитель сохраняет band или контакты. Вектор, его физическая норма и исходные частоты не меняются. Поляризованные комплексные cross-термы сохраняются автоматически как равенство целых матриц, а не выводятся из проверки нескольких вещественных тестов.

(4.5) — дополнительный контроль коэффициентов и двух временных сторон. Он не заменяет конечное sinc-спаривание (4.2) другой более удобной формой.

## 5. Предварительная проверка нового арифметического входа

### 5.1. Большой простой не получает малого множителя

**[ABSTRACT | PAPER]** Если \(U<p\le m\) — простой, то каждый допустимый \(d_i\mid p\), \(d_i\le U\), равен единице. В (3.9) логарифмическая переменная должна быть равна \(p\), иначе логарифм равен нулю. Следовательно,
\[
 Q_{j,U}(p)=\log p\qquad(1\le j\le K),
\]
\[
 \sum_{j=1}^K(-1)^{j-1}\binom Kj Q_{j,U}(p)
   =\left(\sum_{j=1}^K(-1)^{j-1}\binom Kj\right)\log p
   =\log p.
 \tag{5.1}
\]
В (4.2) полный коэффициент такого атома остаётся \(\log p-1\), со **всем** его настоящим матричным весом \(\widetilde a_\ell(p)\).

Это не lower для оператора и не невозможность компенсации с другими \(n\). Оно устанавливает более узкий факт: короткость мёбиусовых переменных **не производит автоматического степенного уменьшения исходного prime-коэффициента**.

### 5.2. Составные сокращаются ровно так, как уже требует \(\Lambda\)

Для различных \(p,q>U\), \(pq\le m\), имеем
\[
 Q_{j,U}(pq)=j\log(pq).
\]
Логарифмический множитель либо содержит оба простых, либо один из них; во втором случае другой размещается в одном из \(j-1\) свободных множителей. Поэтому при \(K\ge2\)
\[
 \sum_{j=1}^K(-1)^{j-1}\binom Kj j\log(pq)=0.
 \tag{5.2}
\]
Более общо, на произведении \(r\) различных простых \(>U\):
\[
 Q_{j,U}(n)=j^{r-1}\log n.
\]
В производственной области \(n\le m\) и (3.7) число таких множителей меньше \(K\). Для \(r\ge2\) соответствующая конечная разность степенного полинома равна нулю. Это восстанавливает \(\Lambda(n)=0\), **не новое сокращение уже prime-supported источника**.

Степени одного большого простого не удаляются. При \(p>U\), \(p^a\le m\):
\[
 Q_{j,U}(p^a)=\binom{a+j-1}{j}\log p,
\]
поскольку коэффициент \(x^a\) в
\((1-x)^{-(j-1)}\sum_{b\ge1}b x^b=x(1-x)^{-(j+1)}\)
равен указанному числу. Полная чередующаяся сумма возвращает **\(\log p\)**, а не \(a\log p\) и не ноль. Коэффициенты с маленькими простыми факторами сохраняются общим точным доказательством (3.6); они не заменяются rough-моделью.

### 5.3. Первая неоплаченная строка

Для реального прогресса понадобилось бы независимо доказать, например,
\[
 \boxed{
 \sup_{\substack{W=PWP\succeq0\\\operatorname{Tr}W=1}}
 \operatorname{Tr}\!\left[
 W\left(\sum_{j=1}^K(-1)^{j-1}\binom Kj\mathcal B_j-\mathcal D_1\right)
 \right]
 \le D_\epsilon m^{\theta(\epsilon)},
 \qquad\theta(\epsilon)\to0.
 }
 \tag{5.3 — UNPROVED}
\]
**Такого неравенства не получено.** По (4.2) это точно старый upper для \(N_\star\), а не новое свойство, которое можно записать в гипотезы и затем объявить доказанным.

Вся доказанная алгебра (3.6),(4.2) остаётся верной для произвольного набора линейных тестовых матриц вместо \(\widetilde a_\ell(n)\). Она ещё не использовала специальную связь достижимой корреляции с actual \(\Lambda-1\) в **неравенстве**. Именно этот дополнительный вход требовал Q41.

Поэтому я **не продолжаю** вывод отдельной нормы каждого \(\mathcal B_j\), не оптимизирую получившуюся сумму положительных цен и не объявляю её заведомо большим остатком новой теоремой. Также не заявляется false-generic или actual-source no-go для всех применений многолинейного раскрытия. Здесь установлено отсутствие вывода в данной попытке, не математическая невозможность его найти.

## 6. Полный бюджет: что оплачено и что осталось прежним

**[COFINAL_FAMILY | PAPER, new exact map with inherited estimates]**

| Элемент | Цена / статус | Что сохранено |
|---|---|---|
| Конечный свёрточный остаток при (3.7) | Ровно 0 | Строгий cutoff, все упорядоченные произведения |
| Подстановка коэффициентов в \(N_\star\) | Ровно 0 | Все оболочки, sinc-тест, \(-1\), верхний атом |
| Новый переход в пространство векторов | Отсутствует | Тот же \(c=Pc\), норма и комплексные cross-термы |
| \(A-N_\star\) | Прежний \(r_\star\le C_\epsilon m^{2\epsilon}\) | Весь Q32-return, один раз |
| Непрерывный фон | Точное \(C^0=A+H_d\), \(0\preceq H_d\preceq4P\) | Не разбивается на большие модули |
| Независимый верх (5.3) | **Не доказан** | Нельзя включить в расходы как известное число |
| Лучший доступный верх \(A\) | Прежний \(s_{\rm keep}\) | Не заменён более слабой новой ценой |

Если бы отдельно был получен \(N_\star\preceq s_\star P\), законный возврат был бы
\[
 A\preceq(s_\star+r_\star)P,
\]
\[
 T_{>R}\preceq(s_\star+r_\star+b_{\rm div})P,
 \qquad
 PK_mP\succeq-[s_\star+r_\star+50L+8]P,
 \tag{6.1}
\]
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\]
Это условная карта потребителя, не установленный \(s_\star\). При \(s_\star=D_\epsilon m^{\theta(\epsilon)}\) полный показатель мог бы быть \(\max\{\theta(\epsilon),2\epsilon\}\); такого нового \(\theta\) нет.

В фактически завершённом расчёте используем только уже принятый upper:
\[
 s_{\rm keep}=W_{<}(m)+W(\lfloor\sqrt m\rfloor),
 \quad
 W(x)=\sum_{2\le n\le x}\frac{\Lambda(n)}{\sqrt n},
 \quad
 W_{<}(m)=\sum_{2\le n<m}\frac{\Lambda(n)}{\sqrt n},
\]
\[
 \boxed{
 A\preceq s_{\rm keep}P,
 \qquad s_{\rm keep}\le6\sqrt m+6m^{1/4}.
 }
 \tag{6.2 — inherited}
\]
И окончательно
\[
 \boxed{
 T_{>R}\preceq[s_{\rm keep}+b_{\rm div}]P,
 \qquad
 PK_mP\succeq-[s_{\rm keep}+50L+8]P.
 }
 \tag{6.3}
\]
Для отчёта о центральной матрице из этого следует лишь
\[
 N_\star\preceq(s_{\rm keep}+r_\star)P.
\]
**Не нужно** после этого возвращаться к \(A\) и искусственно прибавлять ещё один \(r_\star\): (6.2) уже является более прямым исходным результатом.

В прямом \(K\)-возврате отсутствуют повторные \(b_{\rm div}\), \(4\), \(U_{\rm sf}\) или prime-power платы. \(U_{\rm sf}\) вообще не используется в данном пути. Все степени простых находятся внутри точной \(\Lambda\); верхний физический overlap нулевой только в исходной полной форме, а не отдельно в sinc-ядре.

**Полная сохранённая степень остаётся \(1/2\).** Условный прежний показатель \(3/8\) имеет прежнюю зависимость от ZF78; в расчёте Q41 он не использовался и безусловным не объявляется. Новой достаточной оценки на настоящей нулеселективной паре также нет.

## 7. Выполненный rollback, а не новое имя долга

**[ABSTRACT | PAPER]** Чередующаяся сумма в (4.2) собрана обратно **до любого раздельного платежа**:
\[
 \sum_j(-1)^{j-1}\binom Kj\mathcal B_j-\mathcal D_1
 =N_\star,
 \qquad
 C^0=N_\star+E_\star+H_d.
 \tag{7.1}
\]
Добавочная ошибка сборки равна нулю. Вторая формула использует один прежний \(E_\star\).

Таким образом, возвращена именно документированная развилка S5–S6 перед разделением arithmetic Fourier polynomial и matrix test. Не создана новая обязательная «стена короткого обращения». Увеличивать \(K\), уменьшать отдельные коэффициентные нормы или повторять этот preflight с другим названием не обосновано полученным результатом.

### Две сохраняемые записи и их различающие требования

Это не предложение запустить два новых запроса. Это фиксация областей, куда действительно возвращается тот же неоплаченный объект.

| Запись | Точная цена карты | Что могло бы изменить вывод | Стоимость / решающая сила |
|---|---|---|---|
| Полное центральное спаривание \(N_\star\) | \(r_\star=O_\epsilon(m^{2\epsilon})\) до \(A\) | Проверенное совместное неравенство для actual \(\Lambda-1\) и **всех** поляризованных \(\widetilde a_\ell\), а не отдельные нормы | Карта уже оплачена; высокая сила только у нового signed-входа. Его доказательство не получено |
| Конечная физическая \(C^0=A+H_d\) | Точная карта; \(A=C^0-H_d\) | Независимое one-sided сравнение на исходном корреляционном конусе, сохраняющее непрерывную компенсацию | Нет частотной реконструкционной платы; сам знак по-прежнему неоплачен |

**DISCRIMINATOR.** У принятого кандидата должно быть явно выписано первое неравенство, которое использует больше, чем (3.8), и остаётся действительным для общего комплексного \(W=PWP\succeq0\). Коэффициентный контроль на \(p,pq,p^a\) обязан сохранять (5.1)–(5.2). При полной замене дискретного источника непрерывным должны совместно вернуться исходные контакты и \(-H_d\), а не две большие независимые нормы. В настоящем файле такого нового неравенства нет.

### Самое сильное возражение к этому ответу

«Но в поручении просили новый арифметический ход с полезным неравенством, а здесь опять только точное обращение».

**Да. Это возражение по существу верно.** Поэтому ответ имеет `REQUEST_COMPLETION: PARTIAL_NO_NEW_ARITHMETIC_INEQUALITY` и `NO_PROGRESS`, а не статус новой подлеммы-поставщика. Проверенная карта предотвращает незаконный вывод, но не сокращает основной доказательственный долг. Я не подменяю недостающий результат количеством тестов или новым названием формы.

## 8. Реальные проверки и их точная область

**[FINITE_CELL | PAPER; исполненные точные алгебраические controls, не спектральная сертификация]**

Пререгистрация `preregistration.json` создана **после бумажного preflight, но до запуска новых конечных тестов**. Это не ретроактивная регистрация всей работы.

| Прогноз | Итог |
|---|---|
| P1: конечная формула с полным остатком совпадает на всех тестируемых индексах, включая верхний | Подтверждён точными коэффициентными controls |
| P2: при \((U+1)^K>m\) остаток исчезает без удаления prime powers | Подтверждён доказательством поддержки и controls |
| P3: большой простой сохраняет коэффициент \(\log p\), а не малый множитель | Подтверждён (5.1) и controls |
| P4: удаление остатка вне допустимой области будет обнаружено | Обнаружено, в частности коэффициент \(-\log2\) при \(n=54,U=2,K=3\) |

`check_q41.py` использует только стандартную библиотеку Python. Логарифмы представлены **формальными координатами \(\log p\)** с целыми коэффициентами, поэтому не возникает вывода о знаке из float64. Проверены:

- 9 вспомогательных коэффициентных конфигураций, все 816 целых индексов в них; 207 формальных логарифмических координат верхнего индекса;
- 5 дополнительных конфигураций с полным ненулевым остатком;
- rough-prime, semiprime и prime-power подписи;
- 828 рациональных линейных координатных проверок generic complex-Hermitian теста;
- 6 намеренно неверных подстановок, все обнаружены.

**Эти конфигурации не являются production-ячейками исходного \(P\).** Generic Hermitian-контроль проверяет линейный возврат всех координат, а не спектральный знак. Отдельный контроль «raw top zero не означает smoothed top zero» — алгебраический конечный пример, не измерение настоящего Q32-атома. Ничто из этого не заменяет исходниковую оценку (5.3).

`verify_q41_sources.py` проверяет все десять byte/LF/hash frames, UTF-8 и весь канонический хеш. Исторические скрипты не запускает. Код и результаты включены полностью ниже. После сборки Markdown собственные приложения извлечены из него и оба проверяющих повторно исполнены; результат этой процедуры должен совпасть побайтно с включёнными JSON.

**Не выполнялись:** новый независимый математический аудит, Lean, Arb, интервальная сертификация CCM, production-спектральный расчёт, установки пакетов, изменения репозитория или отправка следующего запроса.

## 9. Dependency epistemics и закрытие цикла

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_T_GT_R_UPPER_AND_SPARSE_CCM_RECEIVER
ACTUAL_CONSUMER_REQUIREMENT: >-
  For each sufficiently small fixed epsilon, an original-P upper with exponent
  eta(epsilon)->0 and the complete short/arch return; or an independently
  justified weaker receiver, not supplied in this calculation.
ORIGINAL_REQUESTED_OBJECT: INDEPENDENT_JOINT_SIGNED_SOURCE_INEQUALITY
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_NOTE: >-
  Necessity for RH is not asserted. The all-P consumer remains the requested
  sufficient interface. The repeated-short-inverse representation is not mandatory.
KNOWN_WEAKER_INTERFACES: >-
  S9/S10 retain source-witness receivers in their stated scope. Q41 does not
  supply their missing favorable estimate or promote them to all-P.
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: NONE_CLAIMED_FOR_THE_FINITE_IDENTITY
REOPEN_TRIGGER: >-
  An independent inequality for the complete signed multilinear pairing,
  with hypotheses proved for the actual test/coefficients and a full budget.
MATHEMATICALLY_DEAD: NONE
KILL_SCOPE: NONE
DISCRIMINATOR: >-
  The first source/test-dependent inequality must precede separate sizes and
  remain valid for all complex original-P directions, including the smoothed
  top coefficient and all prime-power signatures.
```

**Что стало меньше?** Основной арифметический долг не уменьшился. Уточнено только, что короткое конечное обращение само по себе не является отсутствующей оценкой.

**Что исключено?** Никакой новой математической семьи или источника. В частности, равенство большого prime-коэффициента единице не запрещает дальнейшего межатомного сокращения. Нового `KILL_*` нет.

**Что не повторять?** Представление (3.8) как уже полученный выигрыш; подстановку (5.3) в предпосылки; удаление остатка без поддержки; отдельное начисление Q32-return каждому каналу; автоматический переход к худшему norm certificate.

**Текущий минимальный долг:** прежний signed upper всей \(N_\star\) / \(C^0\) на исходном \(P\). Новое каталожное имя для него не вводится.

**Одно действие для последующей проверки результата:** подтвердить область (3.6)–(4.6), что все новые результаты являются тождествами, а не арифметическим upper, и что в статус не внесён несуществующий прогресс. Новый математический запрос или запуск иной ветки данным ответом не авторизуется.

```yaml
iteration: Q41
status: NO_PROGRESS
failed_strategy: 'Expecting a signed estimate from short-factor exact inversion alone'
cognitive_operator_used: REPRESENTATION_SHIFT
new_gap_name: NONE_EXISTING_SIGNED_CORE_RETAINED
invariant_learned: >-
  Small individual Mobius variables and exact support cancellation do not
  attenuate the actual large-prime coefficient or determine its coupled form sign.
forbidden_future_move: >-
  Treating the exact expansion, finite coefficient checks, or another separate
  norm bill as the missing arithmetic inequality.
next_decisive_test: 'Applicability and full-return audit of a genuinely additional signed inequality'
route_score_for_this_attempt: 2
RH_CLAIM: NOT_MADE
```

**Итог:** чтение, provenance и конкретный preflight закончены; требуемый новый знаковый арифметический вход не найден. Сохранены полный исходный объект и лучший прежний бюджет. Математическую незавершённость этого шага нельзя скрыть словом «выполнено».

## 10. Полный manifest входных источников

Следующая таблица — измеренные размеры и хеши **каждого полного тела**, без внешнего separator LF. Строки относятся к каноническому TXT, а не к этому ответу.

| ID | Полное имя | Bytes | LF | Строки TXT | SHA-256 |
|---|---|---:|---:|---|---|
| S1 | `CCM_Q40_CONCLUSION.md` | 5988 | 111 | 28–138 | `e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06` |
| S2 | `PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_VERDICT_2026-10-26.md` | 75840 | 1277 | 143–1419 | `6f799885ed9578e2bc0e542b68d340ec62d6c7a0419d415e0f694239e75c9b9e` |
| S3 | `CCM_POST_Q40_COTLAR_PREFLIGHT.md` | 4958 | 90 | 1424–1513 | `d182d10fcb5bde03da833be15c6e7bd1d677559a50e06df457d923bff45bc22b` |
| S4 | `CCM_Q09_AUTOCORRELATION_PREFLIGHT.md` | 4828 | 91 | 1518–1608 | `8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435` |
| S5 | `CCM_POST_Q31_ADDITIVE_FREQUENCY_RETURN.md` | 9712 | 193 | 1613–1805 | `eb6d4c54601a1018097a55d05d7047515d0cfe592fc0983595779fbf79f38243` |
| S6 | `PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_VERDICT_2026-10-26.md` | 77294 | 1247 | 1810–3056 | `1ed7b9b55f29658fa1022f95ef4e89d183be0a1bdac6abaa8ff93cd040fe4f50` |
| S7 | `CCM_Q34_CONCLUSION.md` | 5747 | 99 | 3061–3159 | `acbf977ad791fac2910bea0876969a817ddbd8d57211cf7a4312372c4b6b0e2e` |
| S8 | `CCM_Q17_CONCLUSION.md` | 6633 | 111 | 3164–3274 | `6ab7272567768d77c001ac4855a194a8133911bbecbe56590ca08b570c480f45` |
| S9 | `CCM_Q27_CONCLUSION.md` | 3732 | 70 | 3279–3348 | `5fac209c24bbbe0ec6086d37170ca799da22382d86586e12b8ff54e0ba805e8e` |
| S10 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 | 69 | 3353–3421 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` |

## 11. Воспроизведение собственных приложений

Ниже помещены шесть size/hash-locked приложений: регистрация, полный input manifest, два проверяющих и два полученных JSON. Они не содержат автоматически запускаемых исторических файлов.

Сохрани этот Markdown и исходный TXT. Пример команды для macOS/Linux:

```bash
python3 - \
  PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_VERDICT_2026-10-26.md \
  PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_2026-10-26.txt \
  q41_replay <<'PY'
from pathlib import Path
import hashlib, json, re, subprocess, sys
md, packet, out = Path(sys.argv[1]), Path(sys.argv[2]).resolve(), Path(sys.argv[3])
data = md.read_bytes()
out.mkdir(parents=True, exist_ok=True)
pat = re.compile(rb'^BEGIN_Q41_ASSET ([A-Za-z0-9_.-]+) BYTES=(\d+) SHA256=([0-9a-f]{64})\n```[^\n]*\n', re.M)
assets = {}
for match in pat.finditer(data):
    name = match[1].decode()
    start, size = match.end(), int(match[2])
    body = data[start:start+size]
    if name in assets or len(body) != size or hashlib.sha256(body).hexdigest() != match[3].decode():
        raise ValueError('Asset mismatch: ' + name)
    if data[start+size:start+size+4] != b'```\n':
        raise ValueError('Asset closing fence mismatch: ' + name)
    assets[name] = body
    (out/name).write_bytes(body)
expected = {'preregistration.json', 'q41_source_manifest.json', 'check_q41.py',
            'q41_math_results.json', 'verify_q41_sources.py', 'q41_source_verification.json'}
if set(assets) != expected:
    raise ValueError('Unexpected asset set')
for script, args in [('check_q41.py', []), ('verify_q41_sources.py', [str(packet)])]:
    run = subprocess.run([sys.executable, str((out/script).resolve()), *args],
                         cwd=out, check=True, capture_output=True, text=True)
    (out/(script+'.stdout')).write_text(run.stdout, encoding='utf-8')
for name in ['q41_math_results.json', 'q41_source_verification.json']:
    if (out/name).read_bytes() != assets[name]:
        raise ValueError('Replay differs: ' + name)
print(json.dumps({'assets': len(assets), 'checkers_run': 2,
                  'json_byte_identical': True,
                  'historical_scripts_run': False}, sort_keys=True, indent=2))
PY
```

Первые два аргумента — реальные пути к сохранённому Markdown и каноническому TXT; третий — новый локальный каталог результатов, здесь `q41_replay`. При другом расположении замени, например, первый путь на `"$HOME/Downloads/PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_VERDICT_2026-10-26.md"`. Скрипт не устанавливает зависимости и не пишет в репозиторий.

### `preregistration.json`

BEGIN_Q41_ASSET preregistration.json BYTES=992 SHA256=38f2b858bd783115bb97f5ed464e842142354704469a6faebb25ce805fcd2806
```json
{
  "stage": "After the paper preflight, before executing new finite algebra controls; not a preregistration of the earlier reading or the entire derivation.",
  "request_id": "Q41_EARLIER_FORK_SIGNED_SOURCE",
  "candidate": "Finite repeated short Mobius inversion inside the unchanged complete central pairing",
  "predictions": [
    {"id":"P1","statement":"The finite coefficient identity including the explicit remainder holds for every tested integer n, including n=m."},
    {"id":"P2","statement":"Under (U+1)^k>m the remainder vanishes by support, without dropping actual prime powers."},
    {"id":"P3","statement":"At a prime p>U the full alternating coefficient is log(p), not a small multiple of log(p)."},
    {"id":"P4","statement":"Deleting the remainder outside its support-valid regime is detected by an exact finite control."}
  ],
  "not_predicted": "No CCM spectral sign, exponent gain, independent arithmetic supplier, or RH conclusion is predicted from this algebra."
}
```
END_Q41_ASSET

### `q41_source_manifest.json`

BEGIN_Q41_ASSET q41_source_manifest.json BYTES=2740 SHA256=02c24c4df85cdc3ddfe44d7c010393834dfad72ce4991659b76e82e735cbbdd4
```json
{
  "file": "PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_2026-10-26.txt",
  "bytes": 208316,
  "lf": 3423,
  "sha256": "b311d750de7cca08c919dc77d1665f40a49255914f094b74bf629e9ca6a7b086",
  "sources": [
    {
      "id": "S1",
      "name": "CCM_Q40_CONCLUSION.md",
      "bytes": 5988,
      "lf": 111,
      "sha256": "e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06",
      "start_line": 28,
      "end_line": 138
    },
    {
      "id": "S2",
      "name": "PROSHKA_CCM_SIGNED_BLOCK_COUPLING_Q40_VERDICT_2026-10-26.md",
      "bytes": 75840,
      "lf": 1277,
      "sha256": "6f799885ed9578e2bc0e542b68d340ec62d6c7a0419d415e0f694239e75c9b9e",
      "start_line": 143,
      "end_line": 1419
    },
    {
      "id": "S3",
      "name": "CCM_POST_Q40_COTLAR_PREFLIGHT.md",
      "bytes": 4958,
      "lf": 90,
      "sha256": "d182d10fcb5bde03da833be15c6e7bd1d677559a50e06df457d923bff45bc22b",
      "start_line": 1424,
      "end_line": 1513
    },
    {
      "id": "S4",
      "name": "CCM_Q09_AUTOCORRELATION_PREFLIGHT.md",
      "bytes": 4828,
      "lf": 91,
      "sha256": "8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435",
      "start_line": 1518,
      "end_line": 1608
    },
    {
      "id": "S5",
      "name": "CCM_POST_Q31_ADDITIVE_FREQUENCY_RETURN.md",
      "bytes": 9712,
      "lf": 193,
      "sha256": "eb6d4c54601a1018097a55d05d7047515d0cfe592fc0983595779fbf79f38243",
      "start_line": 1613,
      "end_line": 1805
    },
    {
      "id": "S6",
      "name": "PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_VERDICT_2026-10-26.md",
      "bytes": 77294,
      "lf": 1247,
      "sha256": "1ed7b9b55f29658fa1022f95ef4e89d183be0a1bdac6abaa8ff93cd040fe4f50",
      "start_line": 1810,
      "end_line": 3056
    },
    {
      "id": "S7",
      "name": "CCM_Q34_CONCLUSION.md",
      "bytes": 5747,
      "lf": 99,
      "sha256": "acbf977ad791fac2910bea0876969a817ddbd8d57211cf7a4312372c4b6b0e2e",
      "start_line": 3061,
      "end_line": 3159
    },
    {
      "id": "S8",
      "name": "CCM_Q17_CONCLUSION.md",
      "bytes": 6633,
      "lf": 111,
      "sha256": "6ab7272567768d77c001ac4855a194a8133911bbecbe56590ca08b570c480f45",
      "start_line": 3164,
      "end_line": 3274
    },
    {
      "id": "S9",
      "name": "CCM_Q27_CONCLUSION.md",
      "bytes": 3732,
      "lf": 70,
      "sha256": "5fac209c24bbbe0ec6086d37170ca799da22382d86586e12b8ff54e0ba805e8e",
      "start_line": 3279,
      "end_line": 3348
    },
    {
      "id": "S10",
      "name": "CCM_SPARSE_BAND_RECEIVER.md",
      "bytes": 6174,
      "lf": 69,
      "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
      "start_line": 3353,
      "end_line": 3421
    }
  ]
}
```
END_Q41_ASSET

### `check_q41.py`

BEGIN_Q41_ASSET check_q41.py BYTES=7879 SHA256=c0f15d6f64adbe21b3f386fd8256d2387fd8a675db901c7c971bbfce1ee8ea15
```python
#!/usr/bin/env python3
"""Exact finite controls, not a CCM spectrum computation or a sign certificate.
All logarithms are formal sums of valuations times log(prime). Standard library.
"""
from __future__ import annotations
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


def factors(n: int) -> dict[int, int]:
    result = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            result[d] = result.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def mobius(n: int) -> int:
    fs = factors(n)
    return 0 if any(v > 1 for v in fs.values()) else (-1) ** len(fs)


def conv(a: list[int], b: list[int]) -> list[int]:
    """Literal Dirichlet convolution, with the endpoint n=m included."""
    if len(a) != len(b):
        raise ValueError('Mismatched finite carriers')
    m = len(a) - 1
    c = [0] * (m + 1)
    for d in range(1, m + 1):
        if a[d]:
            for k in range(1, m // d + 1):
                c[d * k] += a[d] * b[k]
    return c


def power(a: list[int], k: int) -> list[int]:
    ans = [0] * len(a)
    ans[1] = 1
    for _ in range(k):
        ans = conv(ans, a)
    return ans


def expansion(m: int, U: int, k: int, *, wrong_sign=False,
              drop_binomial=False, unsigned_mu=False):
    if not 1 <= U <= m or k < 1:
        raise ValueError('Require 1 <= U <= m and k >= 1')
    one = [0] + [1] * m
    unit = [0] * (m + 1)
    unit[1] = 1
    mu = [0] + [mobius(n) for n in range(1, m + 1)]
    u = [0] + [mu[n] if n <= U else 0 for n in range(1, m + 1)]
    if unsigned_mu:
        u = [abs(x) for x in u]
    au = conv(one, u)
    y = [unit[n] - au[n] for n in range(m + 1)]
    total = [0] * (m + 1)
    rows = []
    for j in range(1, k + 1):
        row = conv(power(u, j), power(one, j - 1))
        sign = 1 if wrong_sign else (-1) ** (j - 1)
        coefficient = sign * (1 if drop_binomial else comb(k, j))
        total = [x + coefficient * z for x, z in zip(total, row)]
        rows.append(row)
    return mu, y, power(y, k), total, rows


def log_coordinates(m: int):
    fs = [dict()] + [factors(n) for n in range(1, m + 1)]
    ps = [n for n in range(2, m + 1) if fs[n] == {n: 1}]
    for p in ps:
        ell = [0] + [fs[n].get(p, 0) for n in range(1, m + 1)]
        target = [0] + [int(len(fs[n]) == 1 and p in fs[n])
                        for n in range(1, m + 1)]
        yield p, ell, target


def coefficient_ok(m: int, U: int, k: int, **variant) -> bool:
    mu, y, yk, total, _ = expansion(m, U, k, **variant)
    # For the tested invalid variants, the omitted remainder must be zero
    # under the sufficient strict cutoff. Compare directly with actual Lambda.
    return all(conv(total, ell) == target
               for _, ell, target in log_coordinates(m))


def main():
    configurations = []
    counts = 0
    endpoint_checks = 0
    mixed_checks = 0
    for m, U in [(16, 1), (32, 2), (48, 3), (64, 4),
                 (81, 2), (96, 5), (127, 3), (160, 7), (192, 12)]:
        k = 1
        while (U + 1) ** k <= m:
            k += 1
        mu, y, yk, total, rows = expansion(m, U, k)
        assert all(y[n] == 0 for n in range(1, U + 1))
        assert not any(yk)
        assert total == mu
        for p, ell, target in log_coordinates(m):
            lhs = conv(total, ell)
            assert lhs == target
            endpoint_checks += 1
            assert lhs[m] == target[m]
            # Preserve all four real coordinates of a generic complex
            # Hermitian 2x2 linear test; no actual-P spectral interpretation.
            weights = [lambda n: F((-1) ** n * (n % 5), n + 1),
                       lambda n: F((n % 7) - 3, n + 2),
                       lambda n: F(n, n + 3),
                       lambda n: F((-1) ** n, n + 4)]
            for h in weights:
                assert sum((F(lhs[n]) * h(n) for n in range(1, m + 1)), F()) == \
                       sum((F(target[n]) * h(n) for n in range(1, m + 1)), F())
                mixed_checks += 1
        for n in range(U + 1, m + 1):
            if factors(n) == {n: 1}:
                assert sum((-1) ** (j - 1) * comb(k, j)
                           for j in range(1, k + 1)) == 1
        counts += m
        configurations.append({'m': m, 'U': U, 'k': k,
                               'strict_cutoff': (U + 1) ** k > m})

    # General finite remainder, including invalid support cutoffs.
    general_remainder_configurations = []
    for m, U, k in [(64, 2, 1), (64, 2, 2), (64, 2, 3),
                    (96, 3, 2), (160, 5, 2)]:
        mu, y, yk, total, _ = expansion(m, U, k)
        residual_mu = conv(mu, yk)
        assert [a + b for a, b in zip(total, residual_mu)] == mu
        for _, ell, target in log_coordinates(m):
            residual_lambda = conv(target, yk)
            assert [a + b for a, b in zip(conv(total, ell), residual_lambda)] == target
        general_remainder_configurations.append({'m': m, 'U': U, 'k': k})

    # Explicit rough-prime/rough-product signatures are formal log vectors.
    m, U, k = 125, 2, 5
    _, _, _, _, rows = expansion(m, U, k)
    for p, ell, target in log_coordinates(m):
        if p != 3:
            continue
        for j, row in enumerate(rows, 1):
            coeff = conv(row, ell)
            for a in (1, 2, 3, 4):
                assert coeff[3 ** a] == comb(a + j - 1, j)
        assert conv(expansion(m, U, k)[3], ell)[81] == 1
    m, U, k = 60, 2, 4
    _, _, _, _, rows = expansion(m, U, k)
    for p, ell, _ in log_coordinates(m):
        if p in (3, 5):
            for j, row in enumerate(rows, 1):
                assert conv(row, ell)[15] == j

    planted = {}
    planted['wrong_all_positive_outer_signs'] = not coefficient_ok(64, 2, 4, wrong_sign=True)
    planted['omit_binomial_coefficients'] = not coefficient_ok(64, 2, 4, drop_binomial=True)
    planted['replace_actual_mu_by_absolute_value'] = not coefficient_ok(64, 2, 4, unsigned_mu=True)
    planted['drop_nonzero_remainder'] = not coefficient_ok(64, 2, 3)
    # At n=54=2*3^3 the discarded Lambda*y^3 coefficient of log(2) is -1.
    _, _, yk, total, _ = expansion(64, 2, 3)
    ell2 = next(ell for p, ell, _ in log_coordinates(64) if p == 2)
    lam2 = next(target for p, _, target in log_coordinates(64) if p == 2)
    assert conv(lam2, yk)[54] == -1
    planted['erase_prime_power_coefficient'] = (conv(total, ell2)[4] != 0)
    # Endpoint test: multiplication by the original zero h(m) is distinct
    # from a nonlocal smoothing map. This is an exact generic algebra control.
    h = [F(0), F(2), F(0)]
    smoothing = [[F(1), F(1, 3), F(1, 5)],
                 [F(1, 3), F(1), F(1, 3)],
                 [F(1, 5), F(1, 3), F(1)]]
    top = sum((smoothing[2][j] * h[j] for j in range(3)), F())
    assert top == F(2, 3)
    planted['delete_smoothed_top_from_raw_zero'] = (top != h[2])
    assert all(planted.values())

    result = {
        'status': 'LOCAL_EXACT_CONTROLS_ONLY',
        'actual_lambda_coefficient_configurations': configurations,
        'integer_indices_in_these_configurations': counts,
        'formal_log_endpoint_coordinates': endpoint_checks,
        'generic_hermitian_linear_coordinate_checks': mixed_checks,
        'explicit_remainder_configurations': general_remainder_configurations,
        'rough_prime_and_product_signatures': 'passed',
        'planted_failures_detected': planted,
        'planted_failure_count': len(planted),
        'production_CCM_spectra': False,
        'new_signed_inequality_verified': False,
        'historical_scripts_executed': False
    }
    text = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + '\n'
    Path('q41_math_results.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
```
END_Q41_ASSET

### `q41_math_results.json`

BEGIN_Q41_ASSET q41_math_results.json BYTES=1816 SHA256=2fcd138fe273f9557ac6a6fc24b59d4126f95fbccf0327a03a845042d77cda70
```json
{
  "actual_lambda_coefficient_configurations": [
    {
      "U": 1,
      "k": 5,
      "m": 16,
      "strict_cutoff": true
    },
    {
      "U": 2,
      "k": 4,
      "m": 32,
      "strict_cutoff": true
    },
    {
      "U": 3,
      "k": 3,
      "m": 48,
      "strict_cutoff": true
    },
    {
      "U": 4,
      "k": 3,
      "m": 64,
      "strict_cutoff": true
    },
    {
      "U": 2,
      "k": 5,
      "m": 81,
      "strict_cutoff": true
    },
    {
      "U": 5,
      "k": 3,
      "m": 96,
      "strict_cutoff": true
    },
    {
      "U": 3,
      "k": 4,
      "m": 127,
      "strict_cutoff": true
    },
    {
      "U": 7,
      "k": 3,
      "m": 160,
      "strict_cutoff": true
    },
    {
      "U": 12,
      "k": 3,
      "m": 192,
      "strict_cutoff": true
    }
  ],
  "explicit_remainder_configurations": [
    {
      "U": 2,
      "k": 1,
      "m": 64
    },
    {
      "U": 2,
      "k": 2,
      "m": 64
    },
    {
      "U": 2,
      "k": 3,
      "m": 64
    },
    {
      "U": 3,
      "k": 2,
      "m": 96
    },
    {
      "U": 5,
      "k": 2,
      "m": 160
    }
  ],
  "formal_log_endpoint_coordinates": 207,
  "generic_hermitian_linear_coordinate_checks": 828,
  "historical_scripts_executed": false,
  "integer_indices_in_these_configurations": 816,
  "new_signed_inequality_verified": false,
  "planted_failure_count": 6,
  "planted_failures_detected": {
    "delete_smoothed_top_from_raw_zero": true,
    "drop_nonzero_remainder": true,
    "erase_prime_power_coefficient": true,
    "omit_binomial_coefficients": true,
    "replace_actual_mu_by_absolute_value": true,
    "wrong_all_positive_outer_signs": true
  },
  "production_CCM_spectra": false,
  "rough_prime_and_product_signatures": "passed",
  "status": "LOCAL_EXACT_CONTROLS_ONLY"
}
```
END_Q41_ASSET

### `verify_q41_sources.py`

BEGIN_Q41_ASSET verify_q41_sources.py BYTES=3294 SHA256=3dd7ce253af3b00592b3def84a866fae62fb889fdd05745e84b4fd387b1e74aa
```python
#!/usr/bin/env python3
"""Verify the canonical byte-framed packet. Never execute historical code."""
from __future__ import annotations
from pathlib import Path
import argparse
import hashlib
import json
import re

HEADER = re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n')


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def inspect(data: bytes, expected: dict) -> dict:
    data.decode('utf-8', errors='strict')
    if len(data) != expected['bytes'] or data.count(b'\n') != expected['lf']:
        raise ValueError('Canonical packet byte/LF count differs')
    if digest(data) != expected['sha256']:
        raise ValueError('Canonical packet SHA256 differs')
    marker = b'BEGIN_SOURCE S1 '
    pos = data.find(marker)
    if pos < 0 or (pos and data[pos - 1] != 10):
        raise ValueError('Missing first source frame')
    measured = []
    for index, declared in enumerate(expected['sources'], 1):
        header = HEADER.match(data, pos)
        if header is None or header[1] != f'S{index}'.encode():
            raise ValueError(f'Unexpected source frame at {index}')
        start = header.end()
        end = start + int(header[3])
        body = data[start:end]
        body.decode('utf-8', errors='strict')
        row = {
            'id': header[1].decode(), 'name': header[2].decode(),
            'bytes': len(body), 'lf': body.count(b'\n'),
            'sha256': digest(body),
            'start_line': data[:start].count(b'\n') + 1,
            'end_line': data[:end].count(b'\n')
        }
        if len(body) != int(header[3]) or body.count(b'\n') != int(header[4]):
            raise ValueError(f'Body length differs: S{index}')
        if digest(body) != header[5].decode() or row != declared:
            raise ValueError(f'Body hash or manifest differs: S{index}')
        suffix = f'\nEND_SOURCE S{index}\n'.encode()
        if data[end:end + len(suffix)] != suffix:
            raise ValueError(f'Missing exact separator/end marker: S{index}')
        pos = end + len(suffix)
        while pos < len(data) and data[pos:pos+1] in (b'\n', b'\r', b' ', b'\t'):
            pos += 1
        measured.append(row)
    if pos != len(data):
        raise ValueError('Unparsed trailing material')
    return {
        'canonical_file': expected['file'],
        'canonical_bytes': len(data), 'canonical_lf': data.count(b'\n'),
        'canonical_sha256': digest(data),
        'source_count': len(measured),
        'all_bytes_lf_sha256_and_frames_match': True,
        'all_input_text_utf8': True,
        'historical_code_executed': False,
        'source_proofs_recertified_by_hashing': False
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('canonical_txt', type=Path)
    p.add_argument('--manifest', type=Path,
                   default=Path(__file__).with_name('q41_source_manifest.json'))
    args = p.parse_args()
    expected = json.loads(args.manifest.read_text(encoding='utf-8'))
    result = inspect(args.canonical_txt.read_bytes(), expected)
    text = json.dumps(result, sort_keys=True, indent=2) + '\n'
    Path('q41_source_verification.json').write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
```
END_Q41_ASSET

### `q41_source_verification.json`

BEGIN_Q41_ASSET q41_source_verification.json BYTES=414 SHA256=5f2d62e94587221757dd473a18a1aac5c956e842f0039ecc8a169c6e1419d5e9
```json
{
  "all_bytes_lf_sha256_and_frames_match": true,
  "all_input_text_utf8": true,
  "canonical_bytes": 208316,
  "canonical_file": "PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_2026-10-26.txt",
  "canonical_lf": 3423,
  "canonical_sha256": "b311d750de7cca08c919dc77d1665f40a49255914f094b74bf629e9ca6a7b086",
  "historical_code_executed": false,
  "source_count": 10,
  "source_proofs_recertified_by_hashing": false
}
```
END_Q41_ASSET

