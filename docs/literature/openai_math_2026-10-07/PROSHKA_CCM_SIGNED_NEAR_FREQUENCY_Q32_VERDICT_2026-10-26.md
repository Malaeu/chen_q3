# STATUS: TRY_CCM_SIGNED_NEAR_FREQUENCY_Q32
```yaml
OPERATIVE_CLASS: TRY_CCM_SIGNED_NEAR_FREQUENCY_Q32
VERDICT_CODE: VAUGHAN_ANNULUS_PAID_CENTRAL_SOURCE_TEST_SIGN_NOT_SUPPLIED
DATE: '2026-10-26'
REQUEST_FILE: PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_2026-10-26.txt
REQUEST_COMMIT_AS_SUPPLIED: a52c640752aa0c642bf43cd68dc8f2466ecf9918
REQUEST_BYTES: 126527
REQUEST_LF: 2227
REQUEST_SHA256: cb93c4eca7007eed3dc559c78996a6b3a0c3db3adaff86bc8e0c52eee2bd1b8f
REQUEST_READ: COMPLETE_TOP_REQUEST_AND_SEVEN_COMPLETE_SOURCE_BODIES
SOURCE_MANIFEST: SEVEN_BYTE_COUNTS_AND_SHA256_MATCH
BOOTSTRAP_REPOSITORY: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE: ORIGINAL_FULL_CCM_SAME_THREE_CONTACT_P
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
SELECTED_TRIAL: 'Actual Mangoldt major/minor-arc input inside the exact matrix pairing; retain the central arc and all source/test cross terms until the stated norm completion'
EXTERNAL_INPUT: 'EV: classical Vaughan exponential-sum estimate with q terms, x^(4/5), and conservative log^4'
EXTERNAL_CHECK_SCOPE: 'Statement and hypotheses checked in research PDF arXiv:2505.07803v2, printed p2, equation (1.1) and footnote 1; external proof not independently re-proved'
NOT_USED: 'The new Theorem 1 of that paper; Q31 E1 on Lambda-1; RH; ZF78; Mertens; desired variance'
NEW_PARTIAL_RETURN: 'The annulus X^(-5/8)<=|t|<X^(-1/2) is paid on original P by O_epsilon(m^(2epsilon))'
NEW_FULL_SIGNED_INEQUALITY: NOT_OBTAINED
COMPLETE_TRIAL_POWER: '1/2+epsilon/2, up to fixed logarithms; inferior to the existing elementary half-power upper'
ORIGINAL_P_DIAGNOSTIC: 'A normalized exact five-mode vector has nonzero additive central test coupling on an interval of width 1/(6m); not a lower bound for the Mangoldt-minus-one pairing'
FIRST_SIGN_LOSS: 'Replacing the real, coupled central arithmetic-matrix integral by the integral of separate absolute sizes'
EXECUTED_ROLLBACK: 'Reassemble the full finite centered source C0, then use the already-paid S7 all-P map; no extra contour crossing and no uncharged complement'
PROGRESS_ON_PRIMARY_CONSUMER: NO_PROGRESS
NEW_ETA_EPSILON_TO_ZERO: false
NEW_COEFFICIENT_MARGIN: false
RH: OPEN
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: NONE
LEAN_RUN: false
ARB_RUN: false
PRODUCTION_SPECTRUM_RUN: false
NEW_INDEPENDENT_AUDIT: false
AUTOMATIC_Q33: false
```

# Q32. Ближняя аддитивная полоса: оплаченная внешняя часть и точный отказ центрального импорта

## 0. Результат без повышения статуса

**Требуемое совместное знаковое неравенство не получено.** Испытан один конкретный импорт: классическая оценка Вона для настоящей суммы Мангольдта на аддитивных частотах, применённая к точному матричному спариванию S1.

Получены три проверяемых вывода.

1. Внешняя часть уже сохранённой near-полосы, \(X^{-5/8}\le |t|<X^{-1/2}\), действительно оплачивается величиной \(m^{2\epsilon}\) на **всём исходном P**. Это уменьшает область неоплаченного интеграла, но не показатель полной CCM.
2. На оставшейся центральной полосе выбранный quantitative supplier при законном завершении даёт только полный конверт со степенью \(1/2+\epsilon/2\). Он хуже прежнего \(12\sqrt m\). Оценка **нормы** не объявляется искомым новым совместным знаком.
3. Исходные контакты не зануляют центральный аддитивный тест. Для явного нормированного вектора из того же P доказана ненулевая центральная реакция двух верхних тестовых оболочек на целом интервале частот, а не только в точке \(t=0\). Этот диагностический факт ничего не утверждает о знаке полного спаривания с \(\Lambda-1\).

Первое требование задания — новое неравенство, использующее направленную связь **настоящего источника и настоящего теста сверх их раздельных размеров**, — остаётся невыполненным. В частности, §4 ниже не следует читать как выполнение этого требования: там есть реальная арифметическая оценка, но только для оплачиваемой внешней части. На центральном участке нужного нового свойства я не установил.

Это законченная проверка предложенного способа завершения и его первой неоплаченной строки, а не запрет CCM или всех методов Type-II. Не заявляются мировая новизна, новая область без нулей, SP или RH.

### 0.1. Источник, чтение и зависимость

Канонический TXT прочитан целиком, включая семь полных тел, весь код и приложения S3. Побайтная проверка: **126527 bytes, 2227 LF**, SHA-256 из запроса совпал. Все семь размеров и хешей тел совпали с framing. Манифест и исполнимый проверяющий помещены в конце файла.

Обозначения [S1]–[S7] относятся только к этому каноническому пакету. Унаследованные оценки принимаются в заявленных областях; сообщения о прежних независимых аудитах не выдаются за новый независимый аудит этой работы.

Внешний вход [EV] — классическая оценка Вона:
\[
 \left|\sum_{n\le x}\Lambda(n)e(n\alpha)\right|
 \le C_V\left(\frac{x}{\sqrt q}+x^{4/5}+\sqrt{xq}\right)\log^4(2x),
 \tag{EV}
\]
для \(x\ge2\), \((a,q)=1\), \(1\le q\le x\),
\(|\alpha-a/q|\le q^{-2}\), где \(e(t)=e^{2\pi it}\).

Формулировка проверена по исследовательскому PDF Priyamvad Srivastav, *Log-free bounds on exponential sums over primes*, arXiv:2505.07803v2, printed p. 2, equation (1.1) and footnote 1. Страница просмотрена и как текст, и как изображение. В (1.1) напечатана более сильная логарифмическая степень 3, а сноска прямо указывает версию Вона со степенью 4. Здесь используется последняя, с \(\log(2x)\). Ссылка: `https://arxiv.org/pdf/2505.07803v2`.

Это проверка воспроизведённого в исследовательской статье классического statement, **не утверждение, что заново прочитано оригинальное доказательство Vaughan 1977/1997**. Новый Theorem 1 статьи Сривастава не используется. Все утверждения с [EV] имеют эту явно названную внешнюю теоремную зависимость; элементарные диагнозы §6 и исходниковая проверка от неё не зависят. Q31 E1 к \(\Lambda-1\) не применяется.

## 1. Неизменный объект и полный исходный возврат

**[ABSTRACT | PAPER, definitions and inherited inputs S1, S3, S7]** Фиксируем
\[
 0<\epsilon<1/32,\quad L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,
 \quad \omega_j=2\pi j/L,\quad \Omega=2\pi M/L,\quad K=1+\Omega.
 \tag{1.1}
\]
Сначала фиксируется \(\epsilon\), затем растёт целое m. Все eventual-утверждения имеют общий для всех векторов onset, который может зависеть от \(\epsilon\).

Для \(c=Pc\)
\[
 f(t)=L^{-1/2}\sum_{|j|\le M}c_j e^{i\omega_jt},\quad 0\le t\le L,
 \qquad f=0\text{ вне }[0,L],
\]
\[
 \|f\|_2=\|c\|_2,\quad f(0)=f(L)=0,
 \quad \int_0^L e^{t/2}f(t)dt=\int_0^L e^{-t/2}f(t)dt=0.
 \tag{1.2}
\]
\(Q_M(s)\) — буквальный compression суммы двух нулепродолженных сдвигов. Положим
\[
 h(x)=x^{-1/2}P Q_M(\log x)P,\qquad
 A_m=\sum_{1\le n\le m}\Lambda(n)h(n).
 \tag{1.3}
\]
В частности, \(\Lambda(1)=0\); все \(\Lambda(p^k)=\log p\) остаются.

Входы S1/S3:
\[
 \|h(x)\|\le2x^{-1/2},\quad
 \|h'(x)\|\le(1+2\Omega)x^{-3/2},\quad
 \|h''(x)\|\le C_hK^2x^{-5/2},
 \tag{1.4}
\]
\[
 h(m)=h'(m)=0,\qquad
 \int_1^m h(x)dx=-H_d,\quad 0\preceq H_d\preceq4P.
 \tag{1.5}
\]
Второй endpoint здесь необходим: из одного \(Q_M(L)=0\) не следует законность второго дифференцирования продолжения. Его даёт S1, с исходным \(P\mathbf1=0\); новое граничное условие не вводится.

Пусть
\[
 B=\max(4,\lceil m^{2\epsilon}\rceil),\quad X_j=2^jB,
\]
а J — минимальное целое с \(2X_J\ge m\). Для достаточно поздних m имеем \(2B<m\). Используем **ровно** cutoff S1:
\[
 \chi(v)=1\ (v\le1),\quad \chi(v)=0\ (v\ge2),\quad
 \chi(1+u)=1-10u^3+15u^4-6u^5\ (0<u<1),
\]
\[
 \chi_j(x)=\chi(x/(2X_j))-\chi(x/X_j),\quad
 I_j=[X_j,\min(4X_j,m)]\cap\mathbb Z.
 \tag{1.6}
\]
Тогда \(\chi(x/B)+\sum_{j=0}^J\chi_j(x)=1\) на всем \([1,m]\).

Обозначим
\[
 b_{0,j}(n)=(\Lambda(n)-1)\mathbf1_{I_j}(n),\qquad
 a_j(x)=\chi_j(x)h(x)\mathbf1_{[1,m]}(x).
 \tag{1.7}
\]
**Cutoff один:** он находится в \(a_j\), не второй раз в арифметике. Переменная t ниже двойственна целому n, а не физической координате \(\log n\):
\[
 \widehat b_j(t)=\sum_{n\in I_j}(\Lambda(n)-1)e(-nt),\quad
 \widehat a_j(t)=\sum_{n\in I_j}a_j(n)e(-nt).
 \tag{1.8}
\]

### 1.1. Полный вход S1, не новый результат

Для \(\tau_j=X_j^{-1/2}\)
\[
 N_0=\sum_j\int_{|t|<\tau_j}\widehat b_j(t)\widehat a_j(-t)dt.
 \tag{1.9}
\]
S1 даёт на всем исходном P
\[
 \boxed{A_m=N_0+E_0,\qquad \|E_0\|\le r_0(m)\le C_\epsilon m^{2\epsilon}.}
 \tag{1.10}
\]
Более явная форма принятой цены:
\[
 r_0\le (8+4\Omega)+16\sqrt{2B}
       +C_FK^2(L+1)(J+1).
 \tag{1.11}
\]
Первые два слагаемых оплачивают всю дискретную постоянную модель и smooth base через \(2B\); третье — все прежние far arcs, включая верхнюю оболочку. При \(K\asymp_\epsilon m^\epsilon/L\), \(J+1=O(L)\) правая часть не больше \(C_\epsilon m^{2\epsilon}\).

В (1.10) не применена E1, отсутствует discarded Siegel-character term: используется отдельное точное разложение \(\Lambda=1+(\Lambda-1)\). Модельный атом 1 и его residual \(-1\) сокращаются в полной сборке.

### 1.2. Полный матричный тест

Из (1.4), S1 и точного второго разностного равенства следует с одним абсолютным \(C_a\ge1\):
\[
 \boxed{
 \|\widehat a_j(t)\|
 \le C_a\sqrt X\min\left(1,\frac{K^2}{X^2t^2}\right),
 \quad X=X_j,\quad |t|\le1/2.}
 \tag{1.12}
\]
В точке 0 берётся первая ветвь. Первая оценка — сумма норм \(2/\sqrt n\) по не более чем \(3X+1\) атомам. Для второй
\[
 (1-e(t))^2\widehat a_j(t)=\widehat{\Delta_+^2a_j}(t),\quad
 \sum_n\|\Delta_+^2a_j(n)\|\le\int\|a_j''(x)\|dx,
\]
и \(|1-e(t)|\ge4|t|\). Нулевые value/first-derivative seams в (1.5) исключают дополнительные дельта-члены. Можно взять \(C_a=\max(8,C_{\chi,h}/16)\), где \(C_{\chi,h}\) — константа последнего интегрального входа S1.

Это полная op-норма, без множителя размерности. Для любого \(W=PWP\succeq0\), \(\operatorname{Tr}W=1\), верно
\(|\operatorname{Tr}(W\widehat a_j)|\le\|\widehat a_j\|\). До использования этого неравенства все комплексные mixed entries сохраняются.

## 2. Аудит major/minor-arc гипотез: что законно, а что нет

### 2.1. Точный рациональный выбор вне микроскопического центра

**[FINITE_CELL | PAPER + EV]** Пусть \(X\ge16\), \(2/X\le|t|\le X^{-1/2}\). Для \(t>0\) выберем
\[
 q=\lfloor1/t\rfloor,\quad a=1;
\]
для \(t<0\) возьмём \(a=-1\) с тем же q. Тогда
\[
 \frac1{2|t|}\le q\le\frac1{|t|}\le X/2,
 \quad |t-a/q|<\frac1{q(q+1)}<q^{-2}.
 \tag{2.1}
\]
На двух буквальных префиксах \(Y=\min(4X,m)\) и \(X-1\) условия [EV] выполнены, поскольку \(X-1\ge X/2\). Поэтому разность префиксов, без удаления нижнего атома, даёт
\[
 \boxed{
 |\widehat b_j(t)|\le C_b\ell_X^4
   \left[X\sqrt{|t|}+X^{4/5}+\sqrt{X/|t|}\right],
 \quad \ell_X=\log(8X),}
 \tag{2.2}
\]
где, увеличив абсолютный запас, можно положить \(C_b=16(C_V+1)\).

Дискретная постоянная часть НЕ потеряна. Ее геометрическая сумма имеет модуль не больше \(1/(2|t|)\). На диапазоне \(|t|\ge2/X\) она поглощается \(\sqrt{X/|t|}\). Все веса Мангольдта и prime powers входят в сам [EV].

На оставшемся диапазоне действует только элементарная общая оценка
\[
 |\widehat b_j(t)|\le32X.
 \tag{2.3}
\]
Например, из принятого \(\sum_{n\le x}\Lambda(n)/\sqrt n\le6\sqrt x\) следует \(\psi(x)\le6x\), и \(\sum_{n\in I_j}|\Lambda(n)-1|\le28X\). Запас 32 включает все конечные концы.

### 2.2. Почему центральная полоса не получает minor-arc power бесплатно

**[ABSTRACT | PAPER]** На открытом интервале
\[
 |t|\le1/(100X)
 \tag{2.4}
\]
не существует ненулевого числителя a и знаменателя \(2\le q\le X\), удовлетворяющих \(|t-a/q|\le q^{-2}\). Действительно,
\[
 |t-a/q|\ge1/q-1/(100X)\ge99/(100q)>q^{-2}.
\]
Рациональное приближение \(a=0,q=1\) законно, но [EV] при q=1 имеет цену порядка \(X\log^4X\), не меньшую степень. Подстановка \(q=\lfloor1/|t|\rfloor\) в (2.4) даёт \(q\ge100X\); это вне использованного диапазона \(q\le x\), а даже unrestricted член \(\sqrt{xq}\) был бы большим.

После вычитания постоянной модели
\[
 \widehat b_j(0)=\psi(Y)-\psi(X-1)-(Y-X+1).
 \tag{2.5}
\]
Из оценки модуля \(\sum\Lambda e(nt)\) и отдельной оценки \(\sum e(nt)\) не следует новый знак их разности. Старый scalar-PNT completion из S1 здесь повторно не используется.

**Вывод feasibility-аудита:** [EV] применим к части сохранённой области, но не поставляет новый signed-input для её центра. Это установлено до попытки объявить \(N_0\) малым. Ни одна формула ниже не маркирует весь \(|t|<\tau_j\) как minor arcs.

## 3. Точный центральный объект — до всех модулей

Для произвольного \(0<\lambda\le1/2\) введём
\[
 k_\lambda(d)=\begin{cases}
 2\lambda,&d=0,\\
 \dfrac{\sin(2\pi\lambda d)}{\pi d},&d\ne0.
 \end{cases}
 \tag{3.1}
\]
Конечная Fourier-сборка даёт без ошибки
\[
 \boxed{
 \int_{|t|<\lambda}\widehat b_j(t)\widehat a_j(-t)dt
 =\sum_{n,l\in I_j}(\Lambda(n)-1)a_j(l)k_\lambda(l-n).}
 \tag{3.2}
\]
Для trace с W используется ровно тот же W при всех n,l,j. Нечётная часть частотной интеграции сопряжена с чётной; матрица в (3.2) Hermitian. Это не утверждение о неотрицательности.

Если тестировать буквальную Type-II/делительную структуру, источник (3.2) имеет точную форму
\[
\begin{aligned}
 \mathcal L_j(\lambda)={}&
 \sum_{\substack{d,k\ge1\\dk\in I_j}}
 \mu(d)\log k\,\widetilde a_{j,\lambda}(dk)
 -\sum_{n\in I_j}\widetilde a_{j,\lambda}(n),\\
 \widetilde a_{j,\lambda}(n)={}&
 \sum_{l\in I_j}a_j(l)k_\lambda(l-n).
\end{aligned}
 \tag{3.3}
\]
Здесь применено только доказанное делительным свёртыванием \(\Lambda=\mu*\log\). Формула сама по себе не новый supplier. Все гиперболические ограничения \(dk\le m\), концы \(I_j\), настоящие \(\mu\), \(\log k\), оба времени и полный \(P\) находятся внутри одной суммы. Ни convolution coefficient, ни \(\Lambda(p^k)\) не переопределяются.

**Особенно важный верхний край.** Хотя \(a_j(m)=0\), обычно
\(\widetilde a_{j,\lambda}(m)\ne0\). Поэтому атом \(n=m\) в near-части нельзя удалять отдельно; его законное нулевое исходное значение возвращается только вместе с дополнением. Точно так же нельзя применять к \(\widetilde a\) исходную Euler/contact-лемму для \(h\), не вернув изменившиеся граничные значения. Я такой перенос не делаю.

Будущих арифметических атомов здесь нет: оба индекса n,l явно ограничены \(I_j\subset[1,m]\). Sinc имеет бесконечный носитель как функция аргумента, но это не разрешает продлить арифметическую сумму за m.

На более узком \(\lambda=1/(100X)\) и \(|l-n|\le3X\)
\[
 k_\lambda(l-n)\ge\lambda>0.
 \tag{3.4}
\]
Это следует из интегрирования \(\cos(2\pi t(l-n))\) и \(6\pi/100<\pi/3\). Однако \(\Lambda(n)-1\) знакопеременно, а \(\operatorname{Tr}(Wa_j(l))\) не обязано быть неотрицательным. **Положительный sinc на этом участке не упорядочивает полную mixed-сумму.**

Даже у прямоугольного билинейного подблока \(d\asymp D,k\asymp K_1,DK_1\asymp X\) центральная фаза \(tdk\) меняется лишь на константу при \(|t|=O(1/X)\). Нужная осцилляция не возникает от слова «билинейная». После Cauchy остались бы реальные корреляции \(\mu(d)\mu(d')\) с полным \(\widetilde a(dk)\widetilde a(d'k')\); они здесь не оцениваются предположенным благоприятным знаком.

## 4. Оплаченная внешняя часть near-полосы

**[COFINAL_FAMILY | PAPER + EV]** Выберем один общий для каждого shell cutoff
\[
 \lambda_j=X_j^{-5/8}<\tau_j=X_j^{-1/2},
\]
\[
 N_\star=\sum_j\int_{|t|<\lambda_j}
                 \widehat b_j(t)\widehat a_j(-t)dt,
 \qquad N_0=N_\star+O_{\rm ann}.
 \tag{4.1}
\]
Выбор не зависит от W. На \(\lambda_j\le|t|<\tau_j\) условия (2.2) выполнены eventually; \(X^{-5/8}\ge2/X\) при \(X\ge16\).

Применяя нормы только к **этому** дополнению, из (1.12),(2.2) получаем
\[
\begin{aligned}
 \|O_{{\rm ann},j}\|
 \le C_aC_bK^2\ell_X^4\bigg[
 4X^{-1/2}\lambda_j^{-1/2}
 +2X^{-7/10}\lambda_j^{-1}
 +\frac43X^{-1}\lambda_j^{-3/2}\bigg].
\end{aligned}
 \tag{4.2}
\]
Все три слагаемых получены интегрированием, включая обе стороны \(t>0,t<0\):
\(\int_\lambda^\infty t^{-3/2}=2\lambda^{-1/2}\),
\(\int_\lambda^\infty t^{-2}=\lambda^{-1}\),
\(\int_\lambda^\infty t^{-5/2}=2\lambda^{-3/2}/3\).
Продление положительного верхнего интеграла до бесконечности не продлевает область применимости [EV]: сам supplier использовался лишь на исходном конечном участке.

Подставляя \(\lambda=X^{-5/8}\), получаем степени
\[
 -3/16,\quad -3/40,\quad -1/16.
\]
Следовательно,
\[
 \|O_{{\rm ann},j}\|
 \le8C_aC_bK^2\ell_X^4X^{-1/16}.
 \tag{4.3}
\]
И по всей точной геометрической сетке
\[
 \boxed{
 \|O_{\rm ann}\|\le r_V(m):=
 \frac{8C_aC_b}{1-2^{-1/16}}
 K^2\log^4(8m)B^{-1/16}.}
 \tag{4.4}
\]
При фиксированном \(\epsilon\)
\[
 r_V(m)=O_{\epsilon,V}(m^{15\epsilon/8}L^2)
       \le C_{\epsilon,V}m^{2\epsilon}\quad\text{eventually}.
 \tag{4.5}
\]
Таким образом,
\[
 \boxed{A_m=N_\star+E_\star,\quad
 \|E_\star\|\le r_\star:=r_0+r_V
 \le C_{\epsilon,V}m^{2\epsilon}.}
 \tag{4.6}
\]

**Граница результата.** (4.4) — первая новая количественная арифметическая цена данной попытки: она использует распределение аддитивных фаз настоящей \(\Lambda\) из [EV], а не только \(|\Lambda(n)|\le\log n\). Но тест в её завершении используется через норму (1.12). Это оценка выделенного дополнения, **не** требуемая новая joint sign estimate центральной формы и не изменение полного показателя CCM.

## 5. Законное завершение центра: полный, но недостаточный бюджет

Здесь сначала сохраняется точное \(N_\star\) из (3.2),(4.1). Проверяем, что выбранный supplier даёт при доступном завершении. Это **не** заново введённая PNT-оценка и не E1 для \(\Lambda-1\).

### 5.1. Первая явная потеря joint-фазы

Для \(W\succeq0\), \(W=PWP\), \(\operatorname{Tr}W=1\), завершение использует
\[
\begin{aligned}
 \Re\operatorname{Tr}(WN_\star)
 &\le\sum_j\int_{|t|<\lambda_j}
 |\widehat b_j(t)|\,
 |\operatorname{Tr}(W\widehat a_j(-t))|dt\\
 &\le\sum_j\int_{|t|<\lambda_j}
 |\widehat b_j(t)|\,\|\widehat a_j(-t)\|dt.
\end{aligned}
 \tag{5.1}
\]
**Именно первая строка (5.1) теряет направление совместного знака.** Все mixed coefficients входят в тест до этой строки; они не объявлены нулевыми. Однако направление их связи с арифметической фазой больше не используется. Поэтому (5.1) не отвечает более сильному joint-требованию Q32.

### 5.2. Полный интеграл одного shell

Центр \(|t|<2/X\) по (2.3),(1.12) стоит не более \(128C_a\sqrt X\). Для остальной части используем (2.2), затем замену \(y=X|t|\). Три нужных положительных интеграла вычисляются точно:
\[
\begin{aligned}
 \int_0^\infty y^{1/2}\min(1,K^2/y^2)dy&=\frac83K^{3/2},\\
 \int_0^\infty \min(1,K^2/y^2)dy&=2K,\\
 \int_0^\infty y^{-1/2}\min(1,K^2/y^2)dy&=\frac83\sqrt K.
\end{aligned}
 \tag{5.2}
\]
Следовательно, даже при сохранении всех source terms до (5.1) законно получается лишь
\[
 \boxed{
 \|N_{\star,j}\|
 \le128C_a\sqrt X+
 2C_aC_b\ell_X^4\left[
 \frac83K^{3/2}+2KX^{3/10}+\frac83\sqrt{KX}\right].}
 \tag{5.3}
\]
Интегралы (5.2) являются вычислением положительной allowance; вне исходного диапазона не утверждается новый арифметический bound.

### 5.3. Полная сумма и показатели

Пусть \(D_r=(1-2^{-r})^{-1}\). Поскольку \(X_J<m\),
\(\sum_jX_j^r\le D_rm^r\). Определим явный полный конверт центра
\[
\begin{aligned}
 s_{\rm core}(m)={}&128C_aD_{1/2}\sqrt m\\
 &+2C_aC_b\log^4(8m)\left[
 \frac83(J+1)K^{3/2}+2D_{3/10}Km^{3/10}
 +\frac83D_{1/2}\sqrt{Km}\right].
\end{aligned}
 \tag{5.4}
\]
Тогда
\[
 N_\star\preceq s_{\rm core}P,\qquad
 A_m\preceq s_{\rm trial}P,\quad s_{\rm trial}=s_{\rm core}+r_\star.
 \tag{5.5}
\]

| Сектор полного испытанного сертификата | Цена |
|---|---|
| Начальная constant-model/base/far реконструкция S1 | \(O_\epsilon(m^{2\epsilon})\) |
| Новое внешнее near-кольцо | \(O_{\epsilon,V}(m^{15\epsilon/8}L^2)\) |
| Микроцентр из \(|t|<2/X\) | \(O(\sqrt m)\) |
| Член \(X\sqrt{|t|}\) из [EV] | \(O_V(K^{3/2}L^5)\) |
| Член \(X^{4/5}\) из [EV] | \(O_V(Km^{3/10}L^4)\) |
| Член \(\sqrt{X/|t|}\) из [EV] | \(O_V(\sqrt{Km}L^4)\) |
| Новая ошибка проекции | 0: тест, P и норма не менялись |

На исходном расписании доминирует
\[
 s_{\rm trial}=O_{\epsilon,V}
 \left(m^{1/2+\epsilon/2}L^{7/2}+m^{2\epsilon}\right).
 \tag{5.6}
\]
В частности, показатель не стремится к нулю. Сам положительный сертификат (5.4) уже содержит \(128C_aD_{1/2}\sqrt m\); поэтому его нельзя объявить sub-half-power за счёт изменения словесной интерпретации. **Это нижняя цена только выписанной allowance, не нижняя граница истинного \(N_\star\), \(A_m\) или спектра.**

В применении сохраняем более сильный прежний fallback
\[
 s_{\rm use}=\min\{12\sqrt m,\ s_{\rm trial}\}.
 \tag{5.7}
\]
Не заявляется, что более дорогой новый upper улучшил старую оценку. Q31 \(\sqrt m/L^{1/8}+m^{2\epsilon}\) остаётся отдельно доступным только с его E1-зависимостью. Прежние условные \(3/8\) остаются условными на старую ZF78; ни E1, ни ZF78 в новом выводе не использовались.

## 6. Центральный тест действительно достижим на исходном P

Этот контроль исключает только возможную ошибку «контакты автоматически стирают центральную additive-дугу». Он **не** оценивает арифметическую ошибку \(\Lambda-1\), не утверждает наличие внепрямого нуля и не является новой нижней оценкой CCM.

### 6.1. Точный допустимый вектор

**[COFINAL_FAMILY | PAPER, actual test, no EV]** Пусть \(\omega=2\pi/L\), \(M\ge2\). На \([0,L]\) положим
\[
 u_L(t)=-\frac34+(1+4\omega^2)\cos(\omega t)
              -(\tfrac14+4\omega^2)\cos(2\omega t),
\]
\[
 Z_L=\|u_L\|_2^2
 =L\left(\frac{35}{32}+5\omega^2+16\omega^4\right),\qquad
 f_L=u_L/\sqrt{Z_L}.
 \tag{6.1}
\]
Endpoint равен нулю. Для \(a=\pm1/2\), используя \(\omega L=2\pi\),
\[
 \frac{-3/4}{a}
 +\frac{(1+4\omega^2)a}{a^2+\omega^2}
 -\frac{(1/4+4\omega^2)a}{a^2+4\omega^2}=0.
 \tag{6.2}
\]
Умножение на \(e^{aL}-1\) возвращает буквальные два экспоненциальных интеграла. Поэтому f_L соответствует единичному \(c_L\in\operatorname{ran}P\), с нулями во всех остальных исходных модах. Никакой удобный новый проектор не создаётся.

### 6.2. Настоящий overlap на верхних оболочках

На каждом фиксированном \(0\le t\le\log4\)
\[
 \frac{u_L(t)}{\omega^4t^2}
 \longrightarrow 6-\frac{t^2}{8}
 \quad\text{равномерно, с продолжением при }t=0.
 \tag{6.3}
\]
Это прямое Taylor-разложение конечных косинусов. Правая часть строго больше 5 на этом интервале. Поэтому для достаточно больших L
\(u_L(t)\ge5\omega^4t^2\), \(Z_L\le2L\).

Благодаря периодичности и чётности u_L, для \(0\le s\le\log4\)
\[
\begin{aligned}
 q_L(L-s)&=2\Re\int_0^s\overline{f_L(t)}f_L(t-s)dt\\
 &\ge\frac{5\omega^8}{6L}s^5\ge0.
\end{aligned}
 \tag{6.4}
\]
Вся исходная корреляция сохранена. Для проверки ведущего полинома, если \(p(t)=6t^2-t^4/8\),
\[
 \int_0^s p(t)p(s-t)dt
 =\frac65s^5-\frac1{70}s^7+\frac1{40320}s^9.
 \tag{6.5}
\]
Средний член в (6.5) — настоящий mixed-term, не удаляемая поправка.

### 6.3. Не одна точка, а центральный интервал

Для J≥1 положим \(\theta_{\rm top}=\chi_{J-1}+\chi_J\). Так как
\(m/2\le X_J<m\), ее физический носитель лежит в \([m/4,m]\). При \(x\le m\)
\[
 \theta_{\rm top}(x)=1-\chi(2x/X_J).
\]
На \([3m/4,7m/8]\) имеем \(\theta_{\rm top}\ge1/2\). На всём носителе \(q_L(\log x)\ge0\) по (6.4), а на указанном меньшем интервале
\[
 q_L(\log x)\ge c_0L^{-9},\qquad
 c_0=\frac56(2\pi)^8[\log(8/7)]^5>0.
\]
Следовательно,
\[
 \operatorname{Tr}\left(W_L[\widehat a_{J-1}(0)+\widehat a_J(0)]\right)
 \ge \frac{c_0}{32}\frac{\sqrt m}{L^9},\quad W_L=c_Lc_L^*.
 \tag{6.6}
\]
Все коэффициенты скалярного теста в этой сумме неотрицательны. Для
\(|t|\le1/(12m)\) имеем \(\cos(2\pi nt)\ge1/2\), \(n\le m\). Поэтому
\[
 \boxed{
 \Re\operatorname{Tr}\left(W_L[\widehat a_{J-1}(-t)+\widehat a_J(-t)]\right)
 \ge \frac{c_0}{64}\frac{\sqrt m}{L^9},
 \quad |t|\le\frac1{12m}.}
 \tag{6.7}
\]
Этот интервал находится внутри обеих сохранённых центральных дуг (4.1) для всех поздних m.

**Что доказано:** три контакта не дают нулевой или автоматически дешёвой центральной additive coupling теста. Это настоящий исходный тест с единичной нормой, а не произвольный bump.

**Чего не доказано:** никакая нижняя оценка \(\Re\operatorname{Tr}(W_LN_\star)\). Источники \(\widehat b_j\) различаются между оболочками, имеют свои комплексные фазы, и именно их совместный знак остался неизвестным. Умножать (6.7) на предполагаемый положительный арифметический коэффициент запрещено. Старый endpoint-шаблон используется здесь как проверка применимости, не как объявление нового препятствия полной CCM.

## 7. Полный возврат исходному потребителю

**[COFINAL_FAMILY | PAPER + EV where used]** Исходный делительный R не равен знаменателю q и не равен частотным cutoffs. Его уже оплаченная двухсторонняя цена
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2
 =O_\epsilon(m^{3\epsilon/2}/L+m^{\epsilon/2}+L^2).
 \tag{7.1}
\]
Для любого действительно доказанного upper \(s\) на \(N_\star\)
\[
 \boxed{
 T_{>R}\preceq(s+r_\star+b_{\rm div})P,
 \qquad
 PK_mP\succeq-[s+r_\star+50L+8]P.}
 \tag{7.2}
\]
Это точный input/output: поставленный \(s=D_\epsilon m^{\theta(\epsilon)}\) дал бы \(\max(\theta(\epsilon),2\epsilon)\). В настоящем расчёте поставлен только (5.4), а не \(\theta\to0\).

С сохранённым более выгодным fallback (5.7):
\[
 T_{>R}\preceq(s_{\rm use}+b_{\rm div})P,
 \qquad PK_mP\succeq-[s_{\rm use}+50L+8]P.
 \tag{7.3}
\]

### 7.1. Все обязательные расходы

**P и норма.** Ни один новый тест не вводится в main estimate: все матрицы изначально действуют на том же P. Все W имеют нормировку \(\operatorname{Tr}W=1\); размерностного множителя нет. Дополнительный вектор §6 — лишь явный допустимый диагностический тест, не замена all-P области.

**Два времени и mixed terms.** Они находятся внутри Q_M и полного \(a_j(l)\). В (3.2) не отброшены ни \(n\ne l\), ни межмодовые комплексные члены. Если подставить настоящую пару из S6, все ее self/cross terms и комплексные prefactors остаются внутри полного c. Никакой замены \(\kappa\) его модулем нет.

**Prime powers и μ.** [EV] применяется к \(\Lambda\), включая все proper powers. В (3.3) μ и log соответствуют буквальному конечному произведению dk; \(\Lambda(dk)\) не подставляется вместо произведения или свёртки коэффициентов. Отдельная proper-power плата не добавляется поверх уже полной Λ-оценки.

**Все концы.** Cutoff-перекрытия складываются в 1. Интервалы \(I_j\) конечны, нижний атом X включён, последний shell заканчивается в m, где сохранены оба исходных jets. Нулевое значение исходного n=m не переносится на отдельные near/far части. Неправильный такой перенос обнаруживает exact-контроль в приложении.

**Будущие атомы.** В (3.2) и (3.3) нет n>m; Fourier-gate не разрешает их добавить. Переменная l тоже остаётся в \(I_j\). Не использованы Perron height, бесконечная Λ-сумма или новая contour inversion, поэтому новой finite-height утечки нет.

**Непрерывный фон.** Точный \(\int h=-H_d\) сохраняется. Если source measure буквально dx, центрированный источник равен нулю точно, а не оценивается двумя большими каналами. Для дискретного control \(\Lambda(n)\rightsquigarrow1\) имеем b0=0 и обе near-части исчезают точно; остаётся законная отдельная Euler-модель \(\sum h\), ограниченная \(8+4\Omega\). Это разные, явно различённые controls. В прямой K-оценке лишняя +4 не начисляется.

**Короткий и архимедов расходы.** \(b_{\rm div}\) добавляется один раз только при T_{>R}; архимедова плата \(50L+8\) — один раз при прямом K-return. Не надо дополнительно складывать все прежние расходы Q10/Q31 поверх (7.3).

**Полилогарифмическая пара S6.** Она является отдельно достаточным receiver, а не разрешением заменить all-P. Если только повторить здесь ту же нормовую оценку с \(\Omega_0=O(L)\), она стоит \(O_V(\sqrt mL^{9/2})\) плюс меньшие члены. Отношение allowance к \(m^\delta/L^{2\delta}\) равно \(\gg m^{1/2-\delta}L^{9/2+2\delta}\), что не стремится к нулю для фиксированного \(0<\delta<1/2\). И даже полный исходный \(12\sqrt m\) имеет ту же дефицитную степень. Дешёвый S6-возврат \(o(1)\) этого не меняет. Это проверка данного norm-completion, не запрет source-specific pair estimate.

## 8. Первая неоплаченная строка и выполненный более ранний откат

### 8.1. Конкретный долг

Не доказан направленный верх
\[
 \Re\sum_j\sum_{n,l\in I_j}
 (\Lambda(n)-1)k_{\lambda_j}(l-n)
 \operatorname{Tr}(Wa_j(l))
 \le D_\epsilon m^{\theta(\epsilon)},\qquad \theta(\epsilon)\to0,
 \tag{8.1 OPEN}
\]
равномерно по **тому же** \(W=PWP\succeq0\), \(\operatorname{Tr}W=1\), на общей семье m. Или достаточный более слабый coefficient-margin на настоящей целой паре.

(8.1) — не новая поставленная лемма. Это точная остающаяся обязанность после оплаченного дополнения. [EV] не задаёт ее знак; S1/S3 E1 к \(\Lambda-1\) неприменима; гипотетическая сильная variance из S5 не использовалась.

Для успеха выбранного central Type-II пути требовалось бы реальное неравенство для (3.3), сохраняющее **корреляцию μ(d), log k и самого матричного \(\widetilde a(dk)\)**. Перестановка конечных сумм законна, но не уменьшает ее. В этом ответе такого неравенства нет. Контроль §6 исключает только попытку удалить центральную область через контакты без новой арифметики.

### 8.2. Откат к документированному S7, а не ещё один cutoff

Выбираемый более ранний fork — полный конечный центрированный источник, **до аддитивного Fourier-разделения**:
\[
 C_m^0=A_m+H_d.
\]
Выполненная обратная сборка из (4.6) точна:
\[
 \boxed{C_m^0=N_\star+H_d+E_\star,\qquad\|E_\star\|\le r_\star.}
 \tag{8.2}
\]
Из уже принятого all-P результата S7, не делая нового contour shift,
\[
 A_m=-H_d+V_m-R_{\rm sign}+E_c,
 \quad \|V_m\|\le B_m,\quad\|E_c\|\le e_m,
\]
\[
 B_m=O_\epsilon(m^\epsilon L\log L),\qquad
 e_m=O_\epsilon(m^{-1/4}/L^2).
\tag{8.3}
\]
Следовательно,
\[
 \boxed{
 N_\star=-H_d+V_m-R_{\rm sign}+(E_c-E_\star),
 \quad\|E_c-E_\star\|\le e_m+r_\star.}
 \tag{8.4}
\]
Это точный общий original-P map; неизвестные знаки не поменялись. Дальние контурные края, кратности и фактические source residues остаются ровно теми, что были оплачены S7. Новый контур, зависящий от W, не вводится. Дополнения H0 и cross-blocks отсутствуют, поскольку работа шла на всем P.

Количественно новый upper s для \(N_\star\) дал бы
\[
 R_{\rm sign}\succeq-[s+B_m+e_m+r_\star+4]P,
\]
а lower \(R_{\rm sign}\succeq-dP\) дал бы
\[
 N_\star\preceq[d+B_m+e_m+r_\star]P-H_d.
\]
Все добавочные расходы здесь \(O_{\epsilon,V}(m^{2\epsilon})\). **Ни одна сторона не объявлена независимым источником другой.** Это бухгалтерия выполненного отката, не повторное объявление эквивалентности прорывом.

Причина выбора этого fork конкретна: испытанный norm-completion теряет взаимодействие центра с фактическим тестом. Возврат к C0 прекращает дробление этой связи на independent arithmetic/test sizes и сохраняет ее в исходном линейном источнике. Он не требует платить две большие положительные энергии, variance или inverse norm.

**Нового пригодного источникового неравенства после этого отката я не нашёл.** Поэтому дальнейшая оптимизация \(\lambda_j\), q или логарифмической степени внутри (5.1) не назначается новой попыткой и не объявляется дорогой к доказанному знаку.

### 8.3. Две сохраняемые записи и дискриминатор

Эти записи фиксируются для аудита, не как каталог запускаемых методов:

| Представление | Полная уже оплаченная цена | Проверка, которая может изменить вывод; стоимость |
|---|---|---|
| Конечная совместная sinc/divisor сумма (3.3), то же W | \(r_\star=O_{\epsilon,V}(m^{2\epsilon})\), без future atoms | Проверить первую предлагаемую signed-строку на гиперболических краях и исходном тесте §6. Высокая чувствительность к потере фазы; конечная алгебра, без production spectrum. |
| Выбранный ранний fork C0 и all-P S7 | \(B_m+e_m+r_\star+4=O_{\epsilon,V}(m^{2\epsilon})\) | Проверить, поставлено ли независимое joint-неравенство, а не та же residue/sup-norm цель. Бюджет уже дан; большая контурная вычислительная работа не требуется. |

**DISCRIMINATOR:** любая новая оценка обязана одновременно (i) возвращать нуль для полного centered continuous source, (ii) сохранять (6.7), не утверждая ложное удаление additive-центра, и (iii) указать строку, в которой настоящий \(\Lambda-1\) согласован с фактическим тестом, а не только с его Lp-нормой. Выполнение первых двух controls не заменяет доказательства третьего.

## 9. Статус, самопроверка и завершение

### 9.1. Ledger с областью и способом проверки

| Утверждение | Scope | Verifier | Статус |
|---|---|---|---|
| Исходные P, полная near-реконструкция S1, receiver S6/S7 | ABSTRACT / COFINAL_FAMILY | PAPER, inherited | Использованы в заявленных областях; не пересертифицирован весь upstream chain |
| [EV] | ABSTRACT | PAPER, external theorem statement | Формулировка/применимость просмотрены; внешний proof не воспроизведён |
| (2.1)–(2.3), (3.2)–(3.4) | FINITE_CELL / ABSTRACT | PAPER | Доказаны; не являются самостоятельным signed supplier |
| (4.4)–(4.6) | COFINAL_FAMILY | PAPER + EV | Оплаченная outer-near редукция, не полный выигрыш |
| (5.4)–(5.6), (7.2) | COFINAL_FAMILY | PAPER + EV | Полный недостаточный бюджет выбранного завершения |
| (6.1)–(6.7) | COFINAL_FAMILY | PAPER | Настоящий original-P test diagnostic; не source/CCM lower bound |
| (8.2)–(8.4) | COFINAL_FAMILY | PAPER with inherited S7 | Полный возврат к более раннему источнику; не новый знак |
| (8.1), vanishing exponent, pair margin | COFINAL_FAMILY | CONDITIONAL / UNPROVED | Не использованы как вход и не доказаны |

### 9.2. Самая сильная атака на попытку

**Возражение:** это опять независимые нормы, хотя Q32 требовал нового совместного знака.

**Ответ:** верно для центрального завершения (5.1), поэтому оно здесь и признано неудачным. Исследование установило, где [EV] действительно применяется, оплатило только соответствующую часть и не назвало ее всем ответом. Новый source/test signed-input не найден. Это точный отказ кандидату после его hypothesis/budget map, а не утверждение выполнения первоначальной цели.

**Второе возражение:** большая центральная тестовая реакция не доказывает большой N0.

**Ответ:** верно. §6 говорит только о достижимом тесте и опровергает его автоматическое зануление. Знак \(\widehat b_j\), компенсация оболочек и всю CCM он не оценивает снизу. Синтетические finite-code examples также не считаются production ячейками.

**Третье возражение:** вспомогательная внешняя near-экономия не должна раздувать счётчик прогресса.

**Ответ:** статус по исходному потребителю — **NO_PROGRESS**. Улучшен оплаченный диапазон, но неизвестный знак не стал доказанным. Нет нового полного показателя ниже 1/2, нет coefficient margin, нет результата RH.

### 9.3. Предсказания и фактическая проверка

Prospective registration записана после полного чтения пакета и inspection внешнего statement, до exact-контролей и окончательной сборки доказательства. Ее неизменённое тело включено в приложение.

- P1: гипотезы рационального приближения и незакрытый q=1 центр — подтверждены §2.
- P2: внешняя часть near имеет \(m^{O(\epsilon)}\)-возврат — подтверждено §4; не promoted в полный знак.
- P3: завершённая нормовая цена не дает vanishing exponent — подтверждено §5.
- P4: настоящий исходный тест не удаляет additive-центр — подтверждено §6.
- P5: все необходимые возвраты записываются без смены P — подтверждено §7.

Выполнены **70 точных локальных математических контролей**, обнаружены **8 намеренно внесённых ошибок**. Отдельный стандартный Python-проверяющий подтвердил канонический хеш и все семь тел. Контроли проверяют finite algebra, коэффициенты, cutoffs, полный sinc mixed pairing, действительные prime powers, контакты и рациональные показатели. Они не проверяют асимптотический спектральный знак и не воспроизводят доказательство [EV].

В плане был контроль неверного знака Fourier-инверсии. Для симметричной sinc-дуги одновременная смена всех знаков не меняет ядро, поэтому фиктивного «обнаружения» такого изменения не заявляется. Проверены вместо этого полный второй разностный Fourier-фактор и действительные mixed coefficients. В процессе подготовки удалены три тавтологические bookkeeping-проверки из счётчика; окончательный счёт 70 не включает их.

Lean, Arb, production-спектр, новый независимый аудит и репозиторные записи не запускались. Гипотетическим нулям не назначались численные значения. Код не использует модельный нуль как данные.

### 9.4. Dependency contract и остановка

```yaml
DOWNSTREAM_CONSUMER: original all-P T_>R family with eta(epsilon)->0
ACTUAL_CONSUMER_REQUIREMENT: independent one-sided source upper after complete returns
ORIGINAL_REQUESTED_OBJECT: joint signed near-frequency arithmetic pairing
ORIGINAL_OBJECT_IS: NOT_NECESSARY_AS_A_SEPARATE_REPRESENTATION
KNOWN_WEAKER_INTERFACES:
  - 'Any independent full A upper with vanishing exponent reaches T_>R via (7.2)'
  - 'A genuine actual-pair margin is separately sufficient in S6 scope, not an all-P promotion'
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: exact hypothesis and full-budget test of a classical arithmetic supplier against the localized original matrix
KILL_SCOPE: NONE_FOR_CCM
SCOPED_REJECTED_INFERENCES:
  - 'All retained near frequencies are automatically minor arcs'
  - 'The three original contacts annihilate an additive neighborhood of zero'
  - 'A small outer-near return is a small complete operator'
REOPEN_TRIGGER: 'A proved source-dependent signed comparison before (5.1), with its model, finite endpoints and original-P return paid'
PROGRESS_CLASS_ON_CONSUMER: NO_PROGRESS
ROUTE_SCORE: 2
COGNITIVE_OPERATOR_USED: LITERATURE_BRIDGE
LOOP_DETECTED: independent norm completion repeatedly loses the central source/test phase
FORBIDDEN_FUTURE_MOVE: 'Retune the frequency cutoff or logarithms while retaining (5.1), and call it new arithmetic progress'
CURRENT_GAP: unchanged signed source coupling in the exact finite centered form
NEXT_DECISIVE_TEST: bounded verification of the claimed new source/test inequality, if one is actually supplied; not a requested automatic successor question
AUTOMATIC_Q33: false
```

Пространство и главный потребитель остаются прежними. Для доказательства RH в этом маршруте всё ещё требуется независимый арифметический знак; данный импорт его не поставил.


## Приложение A. Побайтный манифест и происхождение

В таблице указаны только семь тел именно канонического Q32. Хеш целого TXT проверяется отдельно.
Размеры — UTF-8 bytes; LF — число буквальных байтов `0x0a`. Разделительный LF после тела не входит в его размер.

| ID | Файл | Bytes | LF | SHA-256 |
|---|---|---:|---:|---|
| S1 | `CCM_POST_Q31_ADDITIVE_FREQUENCY_RETURN.md` | 9712 | 193 | `eb6d4c54601a1018097a55d05d7047515d0cfe592fc0983595779fbf79f38243` |
| S2 | `CCM_Q31_CONCLUSION.md` | 3988 | 76 | `c1564d3f8a988b605d82ecc468d6c5270c2fcca4e060f352161bb0c6e22526bd` |
| S3 | `PROSHKA_CCM_ACTUAL_IMAGE_DEFICIT_Q31_VERDICT_2026-10-26.md` | 80972 | 1337 | `be40350cff27b1435aa5894c09ed4894b53f7540002f462ab1321c543a204525` |
| S4 | `CCM_Q09_AUTOCORRELATION_PREFLIGHT.md` | 4828 | 91 | `8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435` |
| S5 | `CCM_Q10_MEAN_SQUARE_RETURN.md` | 8007 | 157 | `e5aec69d1dd313fb815f549932ebd7bca0c5f0d52469565ed44266d7fc2679ce` |
| S6 | `CCM_POST_Q26_POLYLOG_WITNESS.md` | 8064 | 154 | `c7db024c1a5b17bcc5af53c427ccd3dd586c12229e4f9306ad045df9f6ba4681` |
| S7 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 | 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` |

Текущий bootstrap прочитан через GitHub connector из `Malaeu/chen_q3`, `rh_clean`,
`docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`; blob
`e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Другие репозиторные файлы здесь не изменялись.
Основные зависимости расчёта: S1 — exact partition, seams, полный constant-model return;
S3 — исходные нормы и контакты; S7 — более ранний all-P map. S4/S5 — границы уже оплаченных
PNT/variance попыток; S6 — только отдельно обозначенный alternative receiver. S2 задаёт статус
предыдущего ответа, но не является доказательством новой оценки.

[EV] проверена по формуле (1.1) и сноске 1 на printed p. 2:
`https://arxiv.org/pdf/2505.07803v2`, Priyamvad Srivastav,
*Log-free bounds on exponential sums over primes*, версия 27 January 2026.
Просмотрены текст и изображение страницы; бинарный PDF-хеш в данном ответе не заявляется.
Сохраняется граница: используется воспроизведённый классический statement Вона, не новый
Theorem 1 этого PDF и не заявленная новая независимая сертификация внешнего доказательства.

## Приложение B. Воспроизведение конечных контролей

Локальная среда запуска: Python 3.13.5, SymPy 1.14.0. Ничего не устанавливалось.
Первый скрипт проверяет только точную конечную алгебру; второй — только байты источника.
Ни один из них не является checker-ом глобального неравенства CCM.

Ниже помещены пять файлов с буквальными длинами и SHA-256. Код извлечения можно сохранить
как `extract_q32.py`; он проверяет каждый вложенный файл до записи. Аргумент 1 — путь к
этому Markdown, аргумент 2 — каталог вывода, например `q32_replay`.

```python
#!/usr/bin/env python3
"""Extract byte-framed Q32 replay files; verifies each length and SHA-256."""
from pathlib import Path
import hashlib,re,sys
if len(sys.argv)!=3:
    raise SystemExit('Usage: python extract_q32.py ANSWER.md OUTPUT_DIRECTORY')
data=Path(sys.argv[1]).read_bytes()
out=Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
pat=rb'^<!-- Q32_ASSET name=([^ ]+) bytes=(\d+) sha256=([0-9a-f]{64}) -->\n```[^\n]*\n'
seen=set()
for hit in re.finditer(pat,data,re.M):
    rawname,rawsize,rawhash=hit.groups(); name=rawname.decode('ascii')
    if Path(name).name!=name or name in seen:
        raise ValueError('Unsafe or duplicate asset name: '+name)
    seen.add(name); size=int(rawsize)
    payload=data[hit.end():hit.end()+size]
    if len(payload)!=size or hashlib.sha256(payload).hexdigest()!=rawhash.decode():
        raise ValueError('Asset checksum mismatch: '+name)
    tail=b'```\n<!-- END_Q32_ASSET -->'
    if data[hit.end()+size:hit.end()+size+len(tail)]!=tail:
        raise ValueError('Asset framing mismatch: '+name)
    (out/name).write_bytes(payload)
if len(seen)!=5:
    raise ValueError('Expected five assets, got '+str(len(seen)))
print('Verified and extracted',len(seen),'Q32 assets')
```

Пример команд — оба длинных имени уже буквальные имена файлов этого запроса и ответа;
ничего внутри них подставлять не нужно. Выполнять из каталога, где сохранены TXT, Markdown
и скопированный `extract_q32.py`:

```bash
python3 extract_q32.py PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_VERDICT_2026-10-26.md q32_replay
uv run --with sympy==1.14.0 python q32_replay/check_q32.py q32_replay/exact_results.replay.json
python3 q32_replay/verify_sources_q32.py PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_2026-10-26.txt q32_replay/source_results.replay.json
cmp q32_replay/exact_results.json q32_replay/exact_results.replay.json
cmp q32_replay/source_results.json q32_replay/source_results.replay.json
```

`uv` в примере нужен только для воспроизведения указанной версии SymPy. В фактически
выполненном локальном запуске использовалась уже существующая среда, без установки.
`cmp` без вывода и с кодом возврата 0 означает побайтное совпадение, не математическую
сертификацию вне области скрипта.

### `registration.json`

<!-- Q32_ASSET name=registration.json bytes=2137 sha256=8fa3e37eada9119a15b26c4bc8abae3b6102427dd94ed521991f94a0cd6f57b5 -->
```json
{
  "task": "Q32_SIGNED_NEAR_FREQUENCY",
  "stage": "After complete canonical packet reading and primary statement inspection; before new exact controls and final proof/budget assembly",
  "mechanism": "Audit a joint major/minor-arc completion using the genuine Mangoldt exponential sum; keep the central matrix pairing exact. Test the original-P central test coupling, and if the source/test sign remains unavailable, roll back to the documented full centered source with its paid all-P map.",
  "import": "Classical Vaughan estimate, power 4/5 and q terms, conservative log^4; statement checked in primary research PDF arXiv:2505.07803v2, printed p2 eq1.1 and footnote1. No new Theorem1 of that paper used.",
  "predictions": [
    {
      "id": "P1",
      "claim": "The rational choice q=floor(1/abs(t)) is admissible away from abs(t) approximately 1/X, but does not supply power cancellation on the microscopic q=1 central arc."
    },
    {
      "id": "P2",
      "claim": "Combining the supplier with the original second-difference test estimate can pay an outer portion of the retained near arcs with m^{O(epsilon)}; this is not the missing full signed estimate."
    },
    {
      "id": "P3",
      "claim": "The complete norm completion still has nonvanishing limiting exponent. Its first phase loss will be made explicit rather than called a joint sign theorem."
    },
    {
      "id": "P4",
      "claim": "A genuine original-P even five-mode vector has nonzero central additive test coupling; contacts do not erase an open neighborhood of t=0."
    },
    {
      "id": "P5",
      "claim": "All source/interval/cutoff and mixed returns can be recorded without changing P; no global sign will be inferred from finite algebra."
    }
  ],
  "planted_failure_plan": [
    "square the shell cutoff",
    "change Fourier inverse sign",
    "drop one off-diagonal complex matrix entry",
    "delete a proper prime power",
    "drop sinc-smoothed top endpoint",
    "use q>X on a prefix",
    "turn fixed logarithm into power saving"
  ],
  "success_not_assumed": true,
  "no_repository_writes": true,
  "no_auto_Q33": true
}
```
<!-- END_Q32_ASSET -->

### `check_q32.py`

<!-- Q32_ASSET name=check_q32.py bytes=7013 sha256=33fbb5bccd3d59f863b4b1e24b7918d1e7270ce8fb729ba9476f4b86820573ca -->
```python
#!/usr/bin/env python3
"""Q32 finite exact controls. Not an asymptotic or actual-CCM certificate.
Python 3 + SymPy. Usage: python check_q32.py results.json
"""
from __future__ import annotations
import json
import sys
from pathlib import Path
import sympy as s

checks: list[str] = []
planted: list[str] = []

def zero(a):
    if isinstance(a, s.MatrixBase):
        return all(s.simplify(v) == 0 for v in a)
    return s.simplify(a) == 0

def eq(name, a, b=0):
    if not zero(a-b):
        raise AssertionError((name, s.simplify(a-b)))
    checks.append(name)

def reject(name, a, b=0):
    if zero(a-b):
        raise AssertionError('undetected planted change: '+name)
    planted.append(name)

def ok(name, condition):
    if not condition:
        raise AssertionError(name)
    checks.append(name)

# The cutoff is carried by the TEST only.
u=s.symbols('u',real=True)
p=1-10*u**3+15*u**4-6*u**5
for j in range(3):
    eq(f'cutoff_jet_left_{j}',s.diff(p,u,j).subs(u,0),1 if j==0 else 0)
    eq(f'cutoff_jet_right_{j}',s.diff(p,u,j).subs(u,1),0)
eq('cutoff_monotonicity_factor',s.diff(p,u),-30*u**2*(1-u)**2)

def chi(x):
    if x<=1:return s.S.One
    if x>=2:return s.S.Zero
    return p.subs(u,x-1)
for x in [s.Rational(5,2),s.Integer(5),s.Integer(7),s.Integer(11),s.Rational(63,2)]:
    B=4; J=2
    eq('partition_'+str(x),chi(x/B)+sum(chi(x/(2*(2**j)*B))-chi(x/((2**j)*B)) for j in range(J+1)),1)
reject('square_cutoff',s.Rational(1,2),s.Rational(1,2)**2)

# Complete matrix Fourier difference identity.
z=s.symbols('z',nonzero=True)
A={1:s.Matrix([[1,2+s.I],[2-s.I,3]]),2:s.Matrix([[2,-s.I],[s.I,-1]]),3:s.Matrix([[0,1],[1,2]])}
Z=s.zeros(2)
Ah=sum((v*z**(-n) for n,v in A.items()),Z)
diff=sum(((A.get(n+2,Z)-2*A.get(n+1,Z)+A.get(n,Z))*z**(-n) for n in range(-1,4)),Z)
eq('full_second_difference_fourier',diff,(1-z)**2*Ah)
# An exact subarc is a sinc kernel, not a diagonal/positive-part replacement.
lam=s.Rational(1,6)
def k(d):
    return 2*lam if d==0 else s.sin(2*s.pi*lam*d)/(s.pi*d)
t=s.symbols('t',real=True)
for d in range(4):
    eq('sinc_integral_'+str(d),s.integrate(s.cos(2*s.pi*d*t),(t,-lam,lam)),k(d))
b={1:-1,2:s.symbols('log2')-1,3:s.symbols('log3')-1}
Bh=sum(v*z**(-n) for n,v in b.items())
prod=s.expand(Bh*Ah.subs(z,1/z))
# Apply the linear interval integration functional to all Laurent coefficients.
via_coeff=s.zeros(2)
for d in range(-2,3):
    via_coeff += prod.applyfunc(lambda v:s.expand(v).coeff(z,d))*k(d)
direct=sum((bn*Al*k(l-n) for n,bn in b.items() for l,Al in A.items()),s.zeros(2))
eq('all_source_test_mixed_pairs',via_coeff,direct)
reject('drop_cross_indices',direct,sum((b[n]*A[n]*k(0) for n in A),s.zeros(2)))
wrong=direct.applyfunc(s.re)
reject('erase_complex_offdiagonal',direct,wrong)
# A zero top does not survive a low pass by itself.
H=s.Matrix([[1,1+s.I],[1-s.I,2]])
smoothed_top=H*k(1)
reject('lowpass_preserves_top_zero',smoothed_top,s.zeros(2))

# Actual arithmetic prime powers and finite Mobius-log reconstruction.
primes=list(s.primerange(2,40)); logs={p:s.Symbol('log'+str(p)) for p in primes}
def logn(n):return sum((v*logs[p] for p,v in s.factorint(n).items()),s.S.Zero)
def mangoldt(n):
    fs=s.factorint(n)
    return logs[next(iter(fs))] if len(fs)==1 else s.S.Zero
for n in range(1,25):
    eq('mu_log_'+str(n),sum(int(s.mobius(d))*logn(n//d) for d in s.divisors(n)),mangoldt(n))
reject('delete_prime_square',mangoldt(4),0)
eq('residual_atom_one',mangoldt(1)-1,-1)
# An interval and a hyperbolic cutoff remain literal in the paired formula.
I=range(4,13)
w={n:sum((Al*k(l-n) for l,Al in A.items()),s.zeros(2)) for n in I}
linear=sum((mangoldt(n)*w[n] for n in I),s.zeros(2))
rebuilt=s.zeros(2)
for d in range(1,13):
    for r in range(1,12//d+1):
        if d*r in w:rebuilt += int(s.mobius(d))*logn(r)*w[d*r]
eq('same_lowpassed_test_hyperbola',linear,rebuilt)

# Rational approximants: they are not legal on the microscopic central arc.
for X,tt in [(100,s.Rational(3,100)),(1000,s.Rational(7,1000)),(10000,s.Rational(9,10000))]:
    q=int(s.floor(1/tt))
    ok('rational_domain_'+str(X),q<=X//2 and abs(tt-s.Rational(1,q))<=s.Rational(1,q*q))
    central=s.Rational(1,100*X)
    badq=int(s.floor(1/central))
    ok('central_large_q_not_admissible_'+str(X),badq>4*X)
    ok('no_nonzero_small_denominator_'+str(X),all(s.Rational(1,q)-central>s.Rational(1,q*q) for q in range(2,40)))

# Original-P even five-mode contact discriminator, entirely symbolic.
om=s.symbols('omega',positive=True)
x=s.symbols('x',real=True)
c0=-s.Rational(3,4); c1=1+4*om**2; c2=-(s.Rational(1,4)+4*om**2)
eq('endpoint_contact',c0+c1+c2)
for a in [s.Rational(1,2),-s.Rational(1,2)]:
    eq('exponential_contact_'+str(a),c0/a+c1*a/(a*a+om*om)+c2*a/(a*a+4*om*om),0)
normal=c0*c0+(c1*c1+c2*c2)/2
eq('physical_norm_polynomial',normal,s.Rational(35,32)+5*om**2+16*om**4)
profile=c0+c1*s.cos(om*x)+c2*s.cos(2*om*x)
lead=s.expand(s.series(profile,om,0,6).removeO()).coeff(om,4)
eq('endpoint_profile_leading_jet',lead,6*x*x-x**4/8)
h=s.symbols('h',positive=True)
overlap=s.integrate(lead*lead.subs(x,h-x),(x,0,h))
eq('all_mixed_endpoint_overlap',overlap,s.Rational(6,5)*h**5-h**7/70+h**9/40320)
reject('drop_quartic_cross_terms',overlap,s.Rational(6,5)*h**5)
eq('top_window_half_weight',chi(s.Rational(3,2)),s.Rational(1,2))

# Exact integral budgets; no data fitting.
y,K=s.symbols('y K',positive=True)
for power,expected,name in [
 (s.Rational(1,2),s.Rational(8,3)*K**s.Rational(3,2),'sqrt_y'),
 (s.Integer(0),2*K,'one'),
 (-s.Rational(1,2),s.Rational(8,3)*s.sqrt(K),'inverse_sqrt_y')]:
    val=s.integrate(y**power,(y,0,K))+K*K*s.integrate(y**(power-2),(y,K,s.oo))
    eq('dual_weight_integral_'+name,val,expected)
for name,lhs,rhs in [
 ('annulus_term1',-s.Rational(1,2)+s.Rational(5,16),-s.Rational(3,16)),
 ('annulus_term2',-s.Rational(7,10)+s.Rational(5,8),-s.Rational(3,40)),
 ('annulus_term3',-1+s.Rational(15,16),-s.Rational(1,16)),
 ('annulus_epsilon',2-2*s.Rational(1,16),s.Rational(15,8))]:eq(name,lhs,rhs)
e=s.symbols('epsilon',positive=True)
eq('full_dominant_power',s.Rational(1,2)+e/2,(1+e)/2)
for ee in [s.S.Zero,s.Rational(1,32)]:
    ok('dominance_check_'+str(ee),s.Rational(1,2)+ee/2>s.Rational(3,10)+ee and s.Rational(1,2)+ee/2>2*ee)
reject('vanishing_power_promotion',s.Rational(1,2)+s.Rational(1,128),s.Rational(1,32))
# End-to-end bookkeeping: exact core error is not a second divisor charge.
A,N,E,Qsmall,Arch=s.symbols('A N E Qsmall Arch')
reject('double_divisor_fee',Arch-N-E,Arch-N-E-Qsmall)

result={'kind':'FINITE_EXACT_ALGEBRA_ONLY_NOT_GLOBAL_CCM_CERTIFICATE',
        'checks':checks,'exact_controls':len(checks),'planted':planted,
        'planted_errors_detected':len(planted),'production_CCM':False,
        'independent_audit':False,'Lean':False,'Arb':False,
        'external_Vaughan_proof_reproved':False}
Path(sys.argv[1] if len(sys.argv)>1 else 'exact_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
print(json.dumps({'exact_controls':len(checks),'planted_errors_detected':len(planted)}))
```
<!-- END_Q32_ASSET -->

### `exact_results.json`

<!-- Q32_ASSET name=exact_results.json bytes=2273 sha256=27b5f65a0de6f2c70e5c35fef99d728a518363e8edab020ab1c4e67f3a5f61ee -->
```json
{
  "Arb": false,
  "Lean": false,
  "checks": [
    "cutoff_jet_left_0",
    "cutoff_jet_right_0",
    "cutoff_jet_left_1",
    "cutoff_jet_right_1",
    "cutoff_jet_left_2",
    "cutoff_jet_right_2",
    "cutoff_monotonicity_factor",
    "partition_5/2",
    "partition_5",
    "partition_7",
    "partition_11",
    "partition_63/2",
    "full_second_difference_fourier",
    "sinc_integral_0",
    "sinc_integral_1",
    "sinc_integral_2",
    "sinc_integral_3",
    "all_source_test_mixed_pairs",
    "mu_log_1",
    "mu_log_2",
    "mu_log_3",
    "mu_log_4",
    "mu_log_5",
    "mu_log_6",
    "mu_log_7",
    "mu_log_8",
    "mu_log_9",
    "mu_log_10",
    "mu_log_11",
    "mu_log_12",
    "mu_log_13",
    "mu_log_14",
    "mu_log_15",
    "mu_log_16",
    "mu_log_17",
    "mu_log_18",
    "mu_log_19",
    "mu_log_20",
    "mu_log_21",
    "mu_log_22",
    "mu_log_23",
    "mu_log_24",
    "residual_atom_one",
    "same_lowpassed_test_hyperbola",
    "rational_domain_100",
    "central_large_q_not_admissible_100",
    "no_nonzero_small_denominator_100",
    "rational_domain_1000",
    "central_large_q_not_admissible_1000",
    "no_nonzero_small_denominator_1000",
    "rational_domain_10000",
    "central_large_q_not_admissible_10000",
    "no_nonzero_small_denominator_10000",
    "endpoint_contact",
    "exponential_contact_1/2",
    "exponential_contact_-1/2",
    "physical_norm_polynomial",
    "endpoint_profile_leading_jet",
    "all_mixed_endpoint_overlap",
    "top_window_half_weight",
    "dual_weight_integral_sqrt_y",
    "dual_weight_integral_one",
    "dual_weight_integral_inverse_sqrt_y",
    "annulus_term1",
    "annulus_term2",
    "annulus_term3",
    "annulus_epsilon",
    "full_dominant_power",
    "dominance_check_0",
    "dominance_check_1/32"
  ],
  "exact_controls": 70,
  "external_Vaughan_proof_reproved": false,
  "independent_audit": false,
  "kind": "FINITE_EXACT_ALGEBRA_ONLY_NOT_GLOBAL_CCM_CERTIFICATE",
  "planted": [
    "square_cutoff",
    "drop_cross_indices",
    "erase_complex_offdiagonal",
    "lowpass_preserves_top_zero",
    "delete_prime_square",
    "drop_quartic_cross_terms",
    "vanishing_power_promotion",
    "double_divisor_fee"
  ],
  "planted_errors_detected": 8,
  "production_CCM": false
}
```
<!-- END_Q32_ASSET -->

### `verify_sources_q32.py`

<!-- Q32_ASSET name=verify_sources_q32.py bytes=1466 sha256=e978924902ed99eea84966fe29ca14579072ae72da17b44f483e9955e3a6f6c7 -->
```python
#!/usr/bin/env python3
"""Verify canonical Q32 bytes and all seven framed bodies. Standard library only."""
from pathlib import Path
import hashlib,json,re,sys
sha=lambda b:hashlib.sha256(b).hexdigest()
p=Path(sys.argv[1] if len(sys.argv)>1 else 'PROSHKA_CCM_SIGNED_NEAR_FREQUENCY_Q32_2026-10-26.txt')
b=p.read_bytes()
assert sha(b)=='cb93c4eca7007eed3dc559c78996a6b3a0c3db3adaff86bc8e0c52eee2bd1b8f'
assert len(b)==126527 and b.count(b'\n')==2227 and b.endswith(b'\n')
b.decode('utf-8')
pat=rb'^=== SOURCE (S\d+): (.*?) \| BYTES (\d+) \| SHA256 ([0-9a-f]{64}) ===\n'
records=[]; last=0
for z in re.finditer(pat,b,re.M):
    sid,name,n,h=z.groups(); n=int(n)
    assert z.start()>=last
    body=b[z.end():z.end()+n]
    assert len(body)==n and sha(body)==h.decode();body.decode('utf-8')
    end=b'\n=== END SOURCE '+sid+b' ==='
    assert b[z.end()+n:z.end()+n+len(end)]==end
    records.append(dict(id=sid.decode(),name=name.decode(),bytes=n,lf=body.count(b'\n'),sha256=h.decode(),start_line=b[:z.end()].count(b'\n')+1,verified=True))
    last=z.end()+n+len(end)
assert [r['id'] for r in records]==[f'S{i}' for i in range(1,8)]
res={'request':{'bytes':len(b),'lf':b.count(b'\n'),'sha256':sha(b),'verified':True},'sources':records,'source_count':7}
Path(sys.argv[2] if len(sys.argv)>2 else 'source_results.json').write_text(json.dumps(res,ensure_ascii=False,indent=2,sort_keys=True)+'\n')
print(json.dumps({'request_verified':True,'sources_verified':len(records)}))
```
<!-- END_Q32_ASSET -->

### `source_results.json`

<!-- Q32_ASSET name=source_results.json bytes=1989 sha256=2c2ae654884397dd393cef8de595c8ef9d17f32072ea5482b1dd02f69a2173be -->
```json
{
  "request": {
    "bytes": 126527,
    "lf": 2227,
    "sha256": "cb93c4eca7007eed3dc559c78996a6b3a0c3db3adaff86bc8e0c52eee2bd1b8f",
    "verified": true
  },
  "source_count": 7,
  "sources": [
    {
      "bytes": 9712,
      "id": "S1",
      "lf": 193,
      "name": "CCM_POST_Q31_ADDITIVE_FREQUENCY_RETURN.md",
      "sha256": "eb6d4c54601a1018097a55d05d7047515d0cfe592fc0983595779fbf79f38243",
      "start_line": 71,
      "verified": true
    },
    {
      "bytes": 3988,
      "id": "S2",
      "lf": 76,
      "name": "CCM_Q31_CONCLUSION.md",
      "sha256": "c1564d3f8a988b605d82ecc468d6c5270c2fcca4e060f352161bb0c6e22526bd",
      "start_line": 268,
      "verified": true
    },
    {
      "bytes": 80972,
      "id": "S3",
      "lf": 1337,
      "name": "PROSHKA_CCM_ACTUAL_IMAGE_DEFICIT_Q31_VERDICT_2026-10-26.md",
      "sha256": "be40350cff27b1435aa5894c09ed4894b53f7540002f462ab1321c543a204525",
      "start_line": 348,
      "verified": true
    },
    {
      "bytes": 4828,
      "id": "S4",
      "lf": 91,
      "name": "CCM_Q09_AUTOCORRELATION_PREFLIGHT.md",
      "sha256": "8714d49b1458a5075d8c3b0b25146ed693b338b01a28ec41247fe3bfabda3435",
      "start_line": 1689,
      "verified": true
    },
    {
      "bytes": 8007,
      "id": "S5",
      "lf": 157,
      "name": "CCM_Q10_MEAN_SQUARE_RETURN.md",
      "sha256": "e5aec69d1dd313fb815f549932ebd7bca0c5f0d52469565ed44266d7fc2679ce",
      "start_line": 1784,
      "verified": true
    },
    {
      "bytes": 8064,
      "id": "S6",
      "lf": 154,
      "name": "CCM_POST_Q26_POLYLOG_WITNESS.md",
      "sha256": "c7db024c1a5b17bcc5af53c427ccd3dd586c12229e4f9306ad045df9f6ba4681",
      "start_line": 1945,
      "verified": true
    },
    {
      "bytes": 5633,
      "id": "S7",
      "lf": 123,
      "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
      "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
      "start_line": 2103,
      "verified": true
    }
  ]
}
```
<!-- END_Q32_ASSET -->


## Приложение C. Фактическая проверка собранного оригинала

После сборки этого Markdown все пять byte-framed файлов повторно извлечены
с проверкой длины и SHA-256. Извлечённый `check_q32.py` выполнен заново: 70 точных
локальных контролей, 8 обнаруженных намеренных ошибок. Извлечённый
`verify_sources_q32.py` заново проверил точный канонический TXT и семь полных тел.
Оба полученных JSON сопоставлены с вложенными через `cmp`: побайтное совпадение.

Машинный YAML заголовок отдельно проверен на синтаксис и совпадение
`OPERATIVE_CLASS` с первой строкой файла. Проверена парность display-math
разделителей и корректность рамок вложений. Это контроль артефакта и локальной
алгебры, не независимый PAPER-аудит полного вывода и не формальная верификация.

**Конечный статус:** полный знаковый центральный арифметический шаг остаётся
непоставленным. Оплаченная внешняя полоса не повышает статус исходной CCM-цели.
