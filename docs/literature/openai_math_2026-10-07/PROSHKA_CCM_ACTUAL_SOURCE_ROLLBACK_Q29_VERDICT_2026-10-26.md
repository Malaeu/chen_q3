# STATUS: TRY_CCM_ACTUAL_SOURCE_ROLLBACK_Q29
```yaml
OPERATIVE_CLASS: TRY_CCM_ACTUAL_SOURCE_ROLLBACK_Q29
VERDICT_CODE: BV_PROGRESSIONS_RETURN_PRINCIPAL_DISCREPANCY_FULL_BUDGET_NO_GAIN
DATE: '2026-10-26'
REQUEST_FILE: PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt
REQUEST_COMMIT_AS_SUPPLIED: 8b878e9bc81ad4c11dffaeab00bb534c3a02eb69
REQUEST_BYTES_OBSERVED: 223966
REQUEST_LF_OBSERVED: 3385
REQUEST_SHA256_OBSERVED: 652b6f8fd2c4b90eb06101fc8bfa0b85f96062c2ee06a9208fdde71f98d97f2e
WHOLE_REQUEST_HASH_SUPPLIED_BY_USER: false
SOURCE_BODIES_READ: 9
SOURCE_BYTE_LOCKS: ALL_NINE_MATCH
BOOTSTRAP: Malaeu/chen_q3; rh_clean; docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
OBJECT: ORIGINAL_FULL_CCM_SAME_THREE_CONTACT_SPARSE_P
SCHEDULE: N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32
SELECTED_PROPERTY: Unconditional Bombieri-Vinogradov distribution of actual von Mangoldt coefficients in reduced arithmetic progressions
SELECTED_TRANSFER: Exact joint matrix reconstruction over all reduced classes, then optimized scalar averaging over auxiliary moduli
EXTERNAL_INPUT_STATUS: CLASSICAL_THEOREM_STATEMENT_VERIFIED_PRIMARY_AUTHOR_PDF; FULL_PROOF_NOT_REAUDITED
EXTERNAL_PDF_RAW_HASH: NOT_VERIFIED; binary download unavailable, web text and page screenshots inspected
BEST_NEW_COMPLETED_BUDGET: "U_BV=O_(a,epsilon)(m^epsilon+(1+Omega)*sqrt(m)/log(m)^(a+1)+log(m)*m^(-epsilon))"
NEW_COMPLETED_POWER: "1/2+epsilon up to fixed logarithms; worse than inherited half-power fallback"
NEW_FAVORABLE_ARITHMETIC_EXPONENT: NONE
NEW_COEFFICIENT_MARGIN: NONE
FIRST_UNPAID_LINE: Independent directed bound for the principal centered matrix after exact reconstruction; BV error averaging does not supply it
EXECUTED_ROLLBACK: Exact removal of redundant residue-class channels before their separate norms; original centered finite matrix recovered with zero extra error
ACTUAL_PRIME_POWER_CORRECTION: Every p^k with p dividing the auxiliary modulus retained; high-block total correction bounded by O(log(m)*m^(-epsilon))
CONTINUOUS_BACKGROUND: Full continuous matrix retained exactly once; equals minus H_decay on the same P
MIXED_TERMS: Full matrix identities throughout; no diagonal replacement and no adjoint/transpose substitution
ORIGINAL_P_RETURN: Identity map on the whole original coefficient space; no new physical projection error
PROGRESS_CLASS: NO_PROGRESS
CONSUMER_PROGRESS: NO_NEW_BOUND
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ACTUAL_ROUTE_KILL_SCOPE: NONE
SCOPED_CERTIFICATE_RESULT: Exact minimax factor 1/sum_(q<=Q)(1/phi(q)) for this scalar reconstruction and this l1 supplier envelope only
EXACT_LOCAL_CONTROLS: 209
PLANTED_ERRORS_DETECTED: 6
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN_RUNS: 0
ARB_RUNS: 0
PRODUCTION_SPECTRAL_RUNS: 0
REPOSITORY_WRITES: NONE
RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED
```

# Q29. Распределение по прогрессиям и цена восстановления полной CCM

## 0. Результат и его граница

**Нового источникового неравенства, которое улучшает полный показатель CCM или поставляет коэффициентный зазор на настоящей паре, я не получил.** Это не вывод о невозможности такого неравенства.

Испытано одно дополнительное количественное свойство настоящей \(\Lambda\), отсутствующее как поставщик в девяти телах текущего пакета: **теорема Бомбьери–Виноградова о распределении по арифметическим прогрессиям**. Это классическая теорема, не новый результат данной работы. Ни тождество Вона из S7, ни Selberg-рекурсия заново не испытываются.

Попытка состоит в том, чтобы разложить **полную центрированную матрицу** по классам остатков, сохранить их общую комплексную матричную зависимость, затем использовать усреднение по модулю. Перенос доведён до всех расходов. Его узкое место вычислено точно:

\[
 \boxed{\text{восстановление требует суммы всех }\varphi(q)
 \text{ классов, а не их среднего}.}
\]

Оптимизация скалярных весов усреднения даёт множитель
\[
 \left(\sum_{q\le Q}\frac1{\varphi(q)}\right)^{-1}
 \asymp\frac1{\log Q},
\]
а не \(Q^{-1}\). До модулей компоненты с нулевой суммой по классам сокращаются точно; общий, или **главный**, арифметический компонент остаётся с коэффициентом один. Теорема контролирует и его, но в используемой форме — с логарифмическим, а не требуемым степенным запасом.

Это **расчёт применимости конкретного внешнего поставщика**, не новое препятствие всем методам прогрессий и не нижняя граница исходного оператора. Нужный знак не объявляется доказанным после простой записи эквивалентной матрицы.

## 1. Источниковая фиксация

### 1.1. Что прочитано и что принято

Прочитан весь канонический TXT, включая код и приложения всех девяти исходников. Верифицированы заявленные размеры и SHA-256 именно тел S1–S9, без разделительного LF. Общий размер и хеш запроса в заголовке **вычислены здесь**: в кратком сообщении пользователя отдельного ожидаемого общего хеша не было. Полный манифест и воспроизводимый проверяющий находятся ниже.

[S1] содержит уже завершённую вероятностную проверку; её положительные энергии и дорогой tilt не используются как новый успех. [S2–S4] сохраняют принятый orbit/all-P возврат. [S5–S8] задают границы предыдущих арифметических и делительных попыток. [S9] отделяет оплаченный higher-order возврат от непоставленной сильной дисперсии. Их upstream-утверждения используются **в ровно записанном объёме**, не объявляются заново независимо сертифицированными.

Ветка CF22/PySR не возобновлялась. Внешний поиск ограничен проверкой выбранного поставщика; отсутствие иных поставщиков в литературе не утверждается.

### 1.2. Исходный объект

**[COFINAL_FAMILY | PAPER; принятый объект S1, S4, S7.]** Фиксируем
\[
 0<\epsilon<1/32,\quad N=m,\quad L=\log m,
 \quad M=R=\lfloor m^\epsilon\rfloor,
 \quad \Omega=\frac{2\pi M}{L}.
\]
Все утверждения ниже относятся к достаточно большим **целым** \(m\); начало может зависеть от фиксированных параметров, но не от вектора.

\(P=P_{m,\epsilon}\) — исходный трёхконтактный ортогональный проектор. Для \(c=Pc\)
\[
 f=F_mc,\qquad
 \|f\|_{L^2(0,L)}=\|c\|_2,
 \qquad f(0)=f(L)=0,
 \qquad\int_0^L e^{\pm t/2}f(t)\,dt=0.
\]
Нулевое продолжение является исходным, не периодическим продолжением при вычислении overlap. Полоса и нормировка не меняются.

Во избежание конфликта с decay-ядром обозначим матричный вес через
\[
 \mathcal H(x)=x^{-1/2}P Q_M(\log x)P,\qquad 1\le x\le m.
 \tag{1.1}
\]
Тогда
\[
 \begin{aligned}
 \mathcal A_m&=\sum_{2\le n\le m}\Lambda(n)\mathcal H(n),\\
 \mathcal C_m^0&=\mathcal A_m-\int_1^m\mathcal H(x)\,dx
              =\mathcal A_m+H_d,\qquad0\preceq H_d\preceq4P.
 \end{aligned}
 \tag{1.2}
\]
\(Q_M(s)=F_m^*(T_s+T_{-s})F_m\) сохраняет обе временные стороны. Все \(\overline c_jc_k\), включая \(j\ne k\), остаются внутри каждой матрицы.

Из S7 наследуются, а также непосредственно следуют из нулевого endpoint:
\[
 \|\mathcal H(x)\|\le2x^{-1/2},\qquad
 \|\mathcal H'(x)\|\le(1+2\Omega)x^{-3/2},\qquad
 \mathcal H(m)=0.
 \tag{1.3}
\]
Действительно, \(\|f'\|_2\le\Omega\|c\|\), а производная каждой сдвиговой билинейной формы ограничена \(\Omega\|c\|\|d\|\). Для двух ориентаций получается \(2\Omega\); дифференцирование \(x^{-1/2}\) добавляет единицу в (1.3). Никакого коммутирования \(P\) со сдвигом не требуется.

## 2. Дополнительный арифметический вход и его точная область

**[ABSTRACT / COFINAL_FAMILY | PAPER; внешний THEOREM, не собственное доказательство BV.]** Для
\[
 \psi(y;q,b)=\sum_{\substack{n\le y\\n\equiv b\pmod q}}\Lambda(n),
 \qquad
 \mathfrak D_q(x)=
 \max_{(b,q)=1}\ \sup_{1\le y\le x}
 \left|\psi(y;q,b)-\frac{y}{\varphi(q)}\right|
\]
используется следующая формулировка из первичных авторских лекционных заметок R. C. Vaughan, *The Bombieri–Vinogradov Theorem*, печатная стр. 3:
\[
 \boxed{
 \sum_{q\le Q}\mathfrak D_q(x)
 \le C_{\mathfrak a}
 \left\{\frac{x}{(\log x)^{\mathfrak a}}
       +\sqrt x\,Q[\log(xQ)]^6\right\},
 \quad 1\le Q\le\sqrt x.
 }
 \tag{2.1}
\]
Здесь \(\mathfrak a>0\) фиксировано; константа не зависит от \(x,Q,b,y\). Все степени простых включены в определение \(\Lambda\) на стр. 1. Утверждение безусловно; GRH, обсуждаемая выше на той же странице, **не является предпосылкой (2.1)**. [W1]

Проверены текст PDF и изображения страниц 3–4; полный внешний proof не воспроизводился. Прямая бинарная загрузка в контейнер не удалась, поэтому raw SHA-256 PDF не заявляется. Это ограничение provenance, не подмена доступной первичной формулировки.

**Что не разрешает (2.1):** произвольные знаковые коэффициенты по классам бесплатно; независимую оценку каждого \(q\) величиной \(Q^{-1}\) от правой части; растущий с \(m\) показатель \(\mathfrak a\) при неизменной константе; положительный операторный знак вместо абсолютной scalar-ошибки. В следующем разделе вся матричная цена будет выведена, а не приписана теореме.

Здесь \(Q\) — вспомогательный предел модулей. Он **не** является исходным \(R\), \(M\), высотой контура или временным параметром пары.

## 3. Полная конечная матрица по классам — до неравенств

**[FINITE_CELL | PAPER; точная конечная алгебра.]** Пусть
\[
 I=(X,Y],\qquad1\le X<Y\le\min(2X,m),
 \quad \mathcal J_I=\int_X^Y\mathcal H(x)\,dx.
\]
Определим
\[
 \begin{aligned}
 \mathcal C_I&=\sum_{X<n\le Y}\Lambda(n)\mathcal H(n)-\mathcal J_I,\\
 \mathcal D_{q,b;I}
 &=\sum_{\substack{X<n\le Y\\n\equiv b\ (q)}}
       \Lambda(n)\mathcal H(n)-\frac{\mathcal J_I}{\varphi(q)},
        \qquad (b,q)=1,\\
 \mathcal B_{q,I}
 &=\sum_{\substack{X<n\le Y\\(n,q)>1}}
        \Lambda(n)\mathcal H(n).
 \end{aligned}
 \tag{3.1}
\]
Для \(q=1\) имеется один класс; \(\mathcal B_{1,I}=0\).

Тогда буквально
\[
 \boxed{
 \mathcal C_I=
 \sum_{b\in(\mathbb Z/q\mathbb Z)^\times}\mathcal D_{q,b;I}
 +\mathcal B_{q,I}.
 }
 \tag{3.2}
\]
Не среднее по \(b\). Каждый допустимый атом входит ровно один раз, а непрерывный фон — \(\varphi(q)\) раз с коэффициентом \(1/\varphi(q)\).

Для любых скалярных \(\beta_q\ge0\) с \(\sum_{q\le Q}\beta_q=1\)
\[
 \boxed{
 \mathcal C_I=
 \sum_{q\le Q}\beta_q
 \left(\sum_{(b,q)=1}\mathcal D_{q,b;I}+\mathcal B_{q,I}\right).
 }
 \tag{3.3}
\]
Пока нет модулей, изменения знаков или вероятностного предположения. (3.3) верно как равенство **всей матрицы**, а значит и при одном и том же \(W=PWP\succeq0\) после взятия следа. Нормировка \(\operatorname{Tr}W\) не меняется.

### 3.1. Невзаимно простые классы — не потерянный остаток

Из настоящей поддержки \(\Lambda\):
\[
 \boxed{
 \mathcal B_{q,I}=
 \sum_{p\mid q}\ \sum_{X<p^k\le Y}\log p\,\mathcal H(p^k).
 }
 \tag{3.4}
\]
Для каждого фиксированного простого \(p\) в \((X,2X]\) находится не более одной степени \(p^k\): отношение двух различных степеней не меньше двух, а нижний конец открыт. Следовательно,
\[
 \boxed{
 \|\mathcal B_{q,I}\|
 \le\frac{2}{\sqrt X}\sum_{p\mid q}\log p
 \le\frac{2\log q}{\sqrt X}.
 }
 \tag{3.5}
\]
При больших \(X\) и \(q\le\sqrt{2X}<X\) эти атомы — собственные степени простых; они **остаются** в (3.4). Их операторный знак не предполагается. Ранее оплаченная proper-power поправка поверх (3.5) не начисляется.

## 4. Первая оценка и все края

**[FINITE_CELL | PAPER.]** Положим
\[
 E_{q,b}(x)=\psi(x;q,b)-x/\varphi(q).
\]
Stieltjes-интегрирование на \((X,Y]\) даёт
\[
 \boxed{
 \mathcal D_{q,b;I}=
 \mathcal H(Y)E_{q,b}(Y)-\mathcal H(X)E_{q,b}(X)
 -\int_X^Y\mathcal H'(x)E_{q,b}(x)\,dx.
 }
 \tag{4.1}
\]
Правая непрерывность \(\psi\), открытый нижний и закрытый верхний конец определяют принадлежность атомов. Если \(Y=m\), первый множитель равен нулю именно потому, что \(Q_M(L)=0\). При других \(Y\) он не удаляется.

Из (1.3):
\[
 \begin{aligned}
 V_{m,I}&:=\|\mathcal H(Y)\|+\|\mathcal H(X)\|
             +\int_X^Y\|\mathcal H'(x)\|\,dx\\
 &\le\frac2{\sqrt Y}+\frac2{\sqrt X}
       +2(1+2\Omega)\left(\frac1{\sqrt X}-\frac1{\sqrt Y}\right)\\
 &=\frac{4(1+\Omega)}{\sqrt X}-\frac{4\Omega}{\sqrt Y}
 \le\frac{4(1+\Omega)}{\sqrt X}=:V_{m,X}.
 \end{aligned}
 \tag{4.2}
\]
Поэтому
\[
 \|\mathcal D_{q,b;I}\|\le V_{m,X}\mathfrak D_q(2X).
 \tag{4.3}
\]
Это полный матричный Abel-return; размерность не умножает норму. Он уже использует модули источниковых ошибок и теряет их фазовую связь с \(\mathcal H'\). Нельзя выдавать последующий вывод за знаковую теорему, которой не содержится в (2.1).

Тем не менее он даёт законный завершённый верх:
\[
 \boxed{
 \|\mathcal C_I\|
 \le V_{m,X}\sum_{q\le Q}\beta_q\varphi(q)\mathfrak D_q(2X)
       +\frac{2\log Q}{\sqrt X}.
 }
 \tag{4.4}
\]
В частности, \(\mathcal C_I\preceq\) правая скалярная часть \(\times P\). Здесь не используется незаконное следствие из покоэффициентного порядка: сначала доказана норма Hermitian-матрицы, затем её односторонний конверт.

## 5. Оптимизация всей скалярной реконструкции

**[ABSTRACT | PAPER; свойство этого способа использования (2.1), не настоящего спектра.]** Введём
\[
 \Sigma_Q=\sum_{q\le Q}\frac1{\varphi(q)}.
\]
Для \(d_q\ge0\), \(\sum d_q\le B\), точная цена линейного функционала равна
\[
 \sup_{\sum d_q\le B}\sum_q\beta_q\varphi(q)d_q
       =B\max_q\beta_q\varphi(q).
 \tag{5.1}
\]
Это elementary duality конечного положительного симплекса. Здесь \(d_q\) — **контроль интерфейса**, не свободно назначаемые настоящие ошибки простых.

Для всех нормированных положительных \(\beta\):
\[
 1=\sum_q\beta_q
 \le\left(\max_q\beta_q\varphi(q)\right)\Sigma_Q.
\]
Равенство достигается при
\[
 \boxed{
 \beta_q=\frac1{\varphi(q)\Sigma_Q},\qquad
 \inf_{\beta}\max_q\beta_q\varphi(q)=\frac1{\Sigma_Q}.
 }
 \tag{5.2}
\]
Разрешение комплексных \(\beta_q\) с \(\sum\beta_q=1\) не улучшает именно norm-completion: применяем треугольник к \(\sum\beta_q\), а поправки получают дополнительную \(\sum|\beta_q|\). Оптимальный положительный выбор уже реализует минимум.

### 5.1. Почему это логарифм, не число модулей

Нужная оценка доказана здесь независимо от вспомогательного пояснения в PDF:
\[
 \frac n{\varphi(n)}=\sum_{d\mid n}\frac{\mu(d)^2}{\varphi(d)}.
 \tag{5.3}
\]
Обе стороны мультипликативны, а на \(p^k\) правая сторона равна
\(1+1/(p-1)=p/(p-1)\). Поэтому, обозначив гармоническую сумму через \(H_j^{\rm harm}\),
\[
 \Sigma_Q=
 \sum_{d\le Q}\frac{\mu(d)^2}{d\varphi(d)}H_{\lfloor Q/d\rfloor}^{\rm harm}.
\]
Все слагаемые неотрицательны и
\[
 \sum_{d\le Q}\frac{\mu(d)^2}{d\varphi(d)}
 \le\prod_p\left(1+\frac1{p(p-1)}\right)
 \le\exp\left(\sum_{n\ge2}\frac1{n(n-1)}\right)=e.
\]
С другой стороны, \(\varphi(q)\le q\). Итого
\[
 \boxed{
 \log(Q+1)\le\Sigma_Q\le e(1+\log Q).
 }
 \tag{5.4}
\]
На печатной стр. 4 [W1] поясняющая строка напечатана с \(\mu(r)\), а не \(\mu(r)^2\); в таком виде равенство неверно уже при \(q=2\). Она **не используется**: (5.3) доказана выше. Это локальная поправка к используемому пояснению, не опровержение теоремы (2.1) и не заявление о полной проверке её доказательства.

Из (4.4), (5.2), (2.1) вытекает полный block-budget:
\[
 \boxed{
 \|\mathcal C_I\|\le
 \frac{4(1+\Omega)C_{\mathfrak a}}{\sqrt X\,\Sigma_Q}
 \left\{\frac{2X}{[\log(2X)]^{\mathfrak a}}
       +\sqrt{2X}\,Q[\log(2XQ)]^6\right\}
 +\frac{2\log Q}{\sqrt X}.
 }
 \tag{5.5}
\]
Ни один положительный запас не появился только от числа \(Q\) модулей. Это точная граница использованного \(\ell^1\)-интерфейса; более тонкая совместная теорема о самих ошибках этим не опровергается.

## 6. Фиксированный выбор параметров и весь диапазон до m

**[COFINAL_FAMILY | PAPER.]** Зафиксируем \(\mathfrak a>0\) и положим для каждого блока
\[
 \ell_X=\log(2X),\qquad
 Q_X=\left\lfloor\frac{\sqrt{2X}}{\ell_X^{\mathfrak a+8}}\right\rfloor.
 \tag{6.1}
\]
При достаточно большом \(X\) имеем \(Q_X\ge2\) и
\[
 \log Q_X\ge\ell_X/4.
\]
Например, достаточно одновременно
\(\sqrt{2X}/\ell_X^{\mathfrak a+8}\ge2\) и
\(\ell_X/4\ge(\mathfrak a+8)\log\ell_X+\log2\).

Поскольку \(Q_X\le\sqrt{2X}\),
\[
 \sqrt{2X}\,Q_X[\log(2XQ_X)]^6
 \le(3/2)^6\frac{2X}{\ell_X^{\mathfrak a+2}}.
\]
Положим \(K_{\mathfrak a}=C_{\mathfrak a}[1+(3/2)^6]\). Из (5.5):
\[
 \boxed{
 \|\mathcal C_{(X,Y]}\|
 \le32K_{\mathfrak a}(1+\Omega)
             \frac{\sqrt X}{\ell_X^{\mathfrak a+1}}
       +\frac{\ell_X}{\sqrt X},
 \quad X<Y\le\min(2X,m).
 }
 \tag{6.2}
\]
Это покрывает **сокращённый последний блок**, а не только полный dyadic block. Потребление supremum в (2.1) законно при каждом его endpoint. Если для последнего блока 2X>m, теорема используется лишь как верх для префиксов t≤Y≤m; никакие атомы m<n≤2X не добавляются в исходную матрицу.

### 6.1. Начальный диапазон

Выбираем
\[
 X_0=2^{\lceil\log_2(m^{2\epsilon})\rceil},
 \qquad m^{2\epsilon}\le X_0<2m^{2\epsilon}.
 \tag{6.3}
\]
Это лишь арифметическая граница суммирования, не новое физическое окно. Для поздних \(m\), \(X_0<m\), и (6.1) допустима для всех последующих блоков.

Из принятых \(\sum_{n\le x}\Lambda(n)/\sqrt n\le6\sqrt x\) и (1.3):
\[
 \begin{aligned}
 \|\mathcal C_{(1,X_0]}\|
 &\le12\sqrt{X_0}+4(\sqrt{X_0}-1)\\
 &\le16\sqrt{X_0}\le16\sqrt2\,m^\epsilon.
 \end{aligned}
 \tag{6.4}
\]
Это единая малая начальная плата; не новая оценка простых и не многократная оплата полного непрерывного фона.

### 6.2. Все большие блоки

Положим \(X_j=2^jX_0<m\), \(Y_j=\min(2X_j,m)\). Интервалы \((X_j,Y_j]\) не пересекаются и вместе с \((1,X_0]\) покрывают все нужные атомы. Для
\[
 G_2=(1-2^{-1/2})^{-1}
\]
имеем
\[
 \sum_j\sqrt{X_j}\le G_2\sqrt m,
 \quad
 \sum_j\frac{\ell_{X_j}}{\sqrt{X_j}}
 \le G_2(L+\log2)m^{-\epsilon},
 \quad \ell_{X_j}\ge2\epsilon L.
\]
Таким образом, доказан полный верх
\[
 \boxed{
 \begin{aligned}
 \|\mathcal C_m^0\|\le U_{\rm BV}(m):={}&
 16\sqrt2\,m^\epsilon\\
 &+\frac{32K_{\mathfrak a}G_2}{(2\epsilon)^{\mathfrak a+1}}
       \frac{(1+\Omega)\sqrt m}{L^{\mathfrak a+1}}\\
 &+G_2(L+\log2)m^{-\epsilon}.
 \end{aligned}
 }
 \tag{6.5}
\]
Все константы независимы от \(m,c,W\) после фиксации \(\epsilon,\mathfrak a\). Численные значения \(C_{\mathfrak a}\) и onset из внешней теоремы здесь не сертифицированы; этот результат PAPER, не конечный интервальный сертификат.

На исходном расписании главный член содержит
\[
 \frac{\sqrt m}{L^{\mathfrak a+1}}
 +\frac{m^{1/2+\epsilon}}{L^{\mathfrak a+2}}.
 \tag{6.6}
\]
**Полная степенная цена этого завершения — \(1/2+\epsilon\), а не \(\eta(\epsilon)\to0\).** Для каждого фиксированного \(\epsilon>0\) и фиксированного \(\mathfrak a\) она в конце концов хуже прежнего \(12\sqrt m\). Выбор очень большого, но фиксированного \(\mathfrak a\) этого не меняет. Выбирать \(\mathfrak a=\mathfrak a(m)\) при неизменных константах теорема не разрешает.

Это сравнение **выписанных конвертов**. В частности, из (6.6) не выводится нижняя оценка фактического \(\|\mathcal C_m^0\|\).

## 7. Почему совместная реконструкция не использовала нужный новый знак

### 7.1. Точный главный компонент, до модулей

**[FINITE_CELL | PAPER.]** Для каждого \(q\) введём
\[
 \psi^{(q)}(x)=\sum_{\substack{n\le x\\(n,q)=1}}\Lambda(n),
 \qquad
 Z_{q,b}(x)=\psi(x;q,b)-\frac{\psi^{(q)}(x)}{\varphi(q)}.
\]
Тогда
\[
 \sum_{(b,q)=1}Z_{q,b}(x)=0,
 \qquad
 E_{q,b}(x)=Z_{q,b}(x)
     +\frac{\psi^{(q)}(x)-x}{\varphi(q)}.
 \tag{7.1}
\]
Это splitting на нулевую по классам и общую компоненты, или на неглавные характеры и главный характер. Для доказательства здесь характеры вообще не требуются.

С тем же **полным** матричным весом определим
\[
 \mathcal Z_{q,b;I}=
 \sum_{\substack{X<n\le Y\\n\equiv b\ (q)}}\Lambda(n)\mathcal H(n)
 -\frac1{\varphi(q)}
   \sum_{\substack{X<n\le Y\\(n,q)=1}}\Lambda(n)\mathcal H(n).
\]
Получаем
\[
 \boxed{
 \mathcal D_{q,b;I}=
 \mathcal Z_{q,b;I}
 +\frac{\mathcal C_I-\mathcal B_{q,I}}{\varphi(q)},
 \qquad \sum_{(b,q)=1}\mathcal Z_{q,b;I}=0.
 }
 \tag{7.2}
\]
Поэтому в точном усреднении (3.3) **вся часть, различающая классы остатков, имеет нулевую суммарную проекцию**. Исходная \(\mathcal C_I\) сохраняет коэффициент \(\sum\beta_q=1\). Настоящие исключённые степени простых возвращаются через \(\mathcal B_{q,I}\).

Неверно говорить, что BV «не содержит никакой информации о главном характере»: он входит в её левую часть. Верный более узкий вывод таков: **в этой реконструкции дополнительная структура различий между классами не создаёт независимого благоприятного знака для главного канала**. После неё доступен только полный предел (5.5), который недостаточен.

### 7.2. Первое неоплаченное неравенство

До (4.3) всё было точным. Для выполнения исходной цели нужно было бы получить меньший направленный верх для
\[
 \operatorname{Tr}\!\left(
 W\sum_I\sum_q\beta_{q,I}
 [\sum_b\mathcal D_{q,b;I}+\mathcal B_{q,I}]
 \right)
 =\operatorname{Tr}(W\mathcal C_m^0),
 \quad W=PWP\succeq0,
 \tag{7.3}
\]
с соответствующей нормировкой и полным бюджетом.

**Такого неравенства из (2.1) не выведено.** В (4.3) связь комплексных overlap-коэффициентов с источниковыми ошибками заменяется их независимой абсолютной вариацией. После этого оптимизация всех \(\beta_q\) честно даёт (5.2), но уже не возвращает потерянный знак.

(7.3) — точное указание неоплаченной строки, **не новая предпосылка и не новый достаточный поставщик**. Ни знак \(Z_{q,b}\), ни независимость ошибок разных \(q\), ни фазовая случайность не принимались.

## 8. Полный возврат к T и K; все сохранённые части

**[COFINAL_FAMILY | PAPER; возврат из S4.]** Из (1.2), (6.5):
\[
 \mathcal A_m\preceq U_{\rm BV}(m)P-H_d.
 \tag{8.1}
\]
С исходным
\[
 b_m=(56+32\Omega)\sqrt R+12(1+\log R)^2
\]
получается
\[
 \boxed{
 T_{>R}\preceq[U_{\rm BV}+b_m]P-H_d,
 \qquad
 PK_mP\succeq H_d-[U_{\rm BV}+50L+8]P.
 }
 \tag{8.2}
\]
Здесь \(b_m\) начисляется только скалярному long-divisor контракту; при прямом возврате полной \(\mathcal A_m\) к \(K_m\) короткая часть не добавляется.

Более сильный прежний \(\mathcal A_m\preceq12\sqrt m P\) сохраняется. Можно взять минимум двух скалярных верхов после удаления благоприятного \(-H_d\), но нельзя одновременно приписать \(-H_d\) старому верху без его доказательства. Поэтому итоговый гарантированный fallback не ухудшается:
\[
 \boxed{
 T_{>R}\preceq[12\sqrt m+b_m]P,
 \qquad
 PK_mP\succeq-[12\sqrt m+50L+8]P.
 }
 \tag{8.3}
\]

| Компонент | Полная цена или точное сохранение | Статус |
|---|---|---|
| Исходная физическая норма и P | Никакой замены теста; карта тождественная | Точно |
| Обе временные ориентации | Внутри каждого \(Q_M(\log n)\) | Точно |
| Все mixed/self-коэффициенты | Внутри полных Hermitian-матриц, не только диагоналей | Точно |
| Невзаимно простые простые степени | (3.4); весь high-range возврат \(\le G_2(L+\log2)m^{-\epsilon}\) | Оплачен |
| Малый диапазон до \(X_0\) | \(16\sqrt2m^\epsilon\) | Оплачен |
| Начальные/конечные атомы блоков | (4.1), интервалы \((X,Y]\) | Оплачены |
| Производственный атом \(n=m\) | Остаётся в сумме; \(Q_M(L)=0\) точно | Сохранён |
| Будущие атомы \(n>m\) | Ни один не введён: все классы и суммы конечны | Нулевая новая плата |
| Непрерывный фон | После сборки ровно \(\int_1^m\mathcal H=-H_d\) | Один раз |
| Новый контур/его хвосты | Не вводился; малые ошибки Q27 не оптимизировались | Нет нового долга |
| Настоящие \(\mu\) при возврате к T | Точный исходный short/long split, \(b_m\) один раз | Принятый вход |
| Архимедова часть | \(50L+8\) только при прямом A→K | Один раз |
| Основной BV-перенос | (6.5), показатель \(1/2+\epsilon\) до выбора старого fallback | Недостаточен |

Возможная настоящая пара \(g,k\) нигде не изменяется, её \(\kappa\) не заменяется модулем и её нормировка не пересчитывается. Доказанные здесь матричные неравенства применяются к уже возвращённому в исходный \(P\) целому вектору; никакой новой карты с дополнительными \(\rho_K,\rho_S\) не вводится. Это **не** новый улучшенный парный бюджет. Прежняя парная цена и условные \(3/8\) под ZF78 остаются в прежнем статусе.

## 9. Выполненный откат и решение по этой попытке

**Сильнейшее возражение:** «После прогрессий ты снова получил обычный абсолютный discrepancy-budget». Да. Именно это показал полный перенос, и это причина записать **NO_PROGRESS по потребителю**, а не выдавать более сложную реконструкцию за успех.

Выполненный откат — **до раздельной оплаты классов**, с удалением введённых прогрессивных каналов по (7.2). Для каждого блока
\[
 \sum_q\beta_q
 \left(\sum_b\mathcal Z_{q,b;I}
       +\mathcal C_I-\mathcal B_{q,I}+\mathcal B_{q,I}\right)
 =\mathcal C_I.
 \tag{9.1}
\]
Возврат к принятому до-нулевому представлению S1/S4 имеет **нулевую добавочную ошибку**:
\[
 \mathcal C_m^0=
 \sum_{n\le m}\Lambda(n)\mathcal H(n)-\int_1^m\mathcal H(x)\,dx.
 \tag{9.2}
\]
Это точный rollback, не новая оценка (9.2). Обоснование, почему идти раньше: в расширении (3.3) исходный потребитель целиком лежит в главном канале; самостоятельно малая неглавная информация не адресует этот потребитель.

**Не найден новый пригодный quantitative supplier, который в данной попытке уменьшает остаточный знак источника.** Найден и проверен дополнительный классический факт о настоящей \(\Lambda\), но его законный ввод-вывод не достигает цели. Это существенно уже, чем утверждение «методы прогрессий бесполезны».

Не следует продолжать эту же scalar-modulus реконструкцию подбором \(Q\), \(\beta_q\), очень большой фиксированной логарифмической степени или точности чисел. Конкретный порог для повторного открытия: **доказанная связь неглавных компонентов с матричным источниковым весом, которая не исчезает при точном восстановлении главного канала и имеет меньшую полную цену**. Нельзя получить её одной заменой \(\sum_b\) на \(\varphi(q)^{-1}\sum_b\).

Две точные координаты одной развилки, а не список новых кампаний:

| Представление | Что сохраняет / чему учит | Различающая сила и цена |
|---|---|---|
| Разложение по \(q,b\) с полным (7.2) | Видно, что новый неглавный сектор имеет нулевой суммарный коэффициент | Высокая против ложного \(1/Q\)-выигрыша; малый конечный algebra-cost; выполнено |
| Исходная \(\mathcal C_m^0\) до расширения | Сохраняет ненулевую знаковую связь \(\Lambda\) с полной автокорреляцией | Не закрывает знак; нулевая цена обратного перехода; выбранный rollback |

Ни одна строка таблицы не назначается новым доказанным арифметическим входом. Истинный источник может иметь сокращение, не описываемое (4.3); оно здесь не выведено и не запрещено.

## 10. Границы проверки, прогнозы и эпистемический журнал

### 10.1. Исполняемые проверки

Выполнены **209 exact-локальных контролей**; обнаружены **шесть намеренных ошибок**. Проверены действительные коэффициентные данные поддержки \(\Lambda(p^k)=\log p\) с формальными логарифмами, все классы и исключённые степени, комплексные off-diagonal entries общей тестовой матрицы, обе границы Stieltjes-return, minimax и точные степени.

Тестовая матрица в коде — полиномиальная Hermitian-матрица с комплексными смешанными элементами. Она проверяет универсальные конечные тождества; **это не производственная CCM и не численная оценка её спектра**. Проверка манифеста отдельно удостоверяет девять входных тел. После сборки ответа все шесть встроенных файлов повторно извлечены по размерам и хешам; оба проверяющих исполнены из извлечённых копий, оба JSON-результата совпали побайтно. Ранее заявленные независимые аудиты исходников не выдаются за новый аудит этого вывода.

Регистрация записана после чтения и начального PAPER-вывода, но **до** новых executable-контролей. Это не задним числом предсказанный математический успех. Судьба P1–P3: подтверждены exact-кодом и приведёнными доказательствами. P4: полный показательный расчёт подтвердил отсутствие выигрыша у выбранного завершения. Новый RH-результат не предсказывался.

**DISCRIMINATOR:** потеря \(\varphi(q)\), \(\mathcal B_{q,I}\), хотя бы одного endpoint или off-diagonal entry нарушает точную конечную реконструкцию. Для заявленного улучшения нужен не почти нулевой численный остаток, а односторонний верх всей исходной \(\mathcal C_m^0\) после её возврата. Повышение precision не меняет символические множители (5.2) и (6.6).

### 10.2. Ledger

| ID | Утверждение | Scope | Verifier | Область |
|---|---|---|---|---|
| IN | Источник/P, continuous identity, short/arch, прежний fallback | COFINAL_FAMILY | PAPER | Принятые входы S1/S4/S7, без повышения upstream-статуса |
| BV | (2.1) для настоящей \(\Lambda\) | COFINAL_FAMILY | PAPER | Внешняя классическая теорема; первичное statement проверено |
| MAP | (3.1)–(3.4), (4.1), (7.2) | FINITE_CELL | PAPER | Точные полные матрицы и все коэффициенты |
| PP | (3.5) и high-range сумма | COFINAL_FAMILY | PAPER | Реальные исключённые степени простых, не весь источник |
| OPT | (5.1)–(5.4) | ABSTRACT | PAPER | Оптимум указанного scalar/l1 интерфейса, не спектральный no-go |
| RETURN | (6.5), (8.2) | COFINAL_FAMILY | PAPER | Полный, но недостаточный бюджет |
| TARGET | \(\eta(\epsilon)\to0\), коэффициентный запас | COFINAL_FAMILY | CONDITIONAL | OPEN; не использовались как вход |

**DOWNSTREAM_CONSUMER:** исходный all-P sparse-band верх \(T_{>R}\), а не заменённый H0.

**ACTUAL_CONSUMER_REQUIREMENT:** \(C_\epsilon m^{\eta(\epsilon)}P\), \(\eta(\epsilon)\to0\), со всеми возвратами и общими ячейками. Допустимый парный receiver остаётся альтернативой, но новый запас по нему не доказан.

**ORIGINAL_REQUESTED_OBJECT:** дополнительное quantitative source-property и его полный source-preserving перенос. **ORIGINAL_OBJECT_IS:** NOT_NECESSARY для данного конкретного BV/sup-norm completion; это выбранный достаточный механизм, не обязательная форма цели.

**KNOWN_WEAKER_INTERFACES:** прямой односторонний верх всей \(\mathcal C_m^0\); независимая более слабая парная оценка с оплаченной нормой. Они не поставлены тем фактом, что их можно записать.

**FAILURE_TYPE:** NO_DERIVATION. **EPISTEMIC_STATUS:** RESEARCH_DEBT. **KILL_SCOPE для настоящей CCM:** NONE. Абстрактный minimax не повышается до математической невозможности источника.

**NOVELTY_AXIS:** новый для данного приложенного набора источников trial внешней теоремы о прогрессиях; количественное отображение её кванторов на буквальную матрицу. Историческая новизна BV, partial summation, character decomposition или totient identity не утверждается.

**Что стало меньше:** для выбранного BV-импорта больше нет неопределённости, где теряется мнимый выигрыш от числа модулей и сколько стоит точная реконструкция. **Что не стало меньше:** доказанный полный арифметический показатель исходной цели. Поэтому consumer progress — NO_PROGRESS, не PROOF_PROGRESS.

```yaml
MEMORY_ENTRY:
  iteration: Q29_ACTUAL_SOURCE_BV_TRANSFER
  status: OPEN
  cognitive_operator_used: LITERATURE_BRIDGE
  bridge_kind: ONE_WAY_TRANSFER
  chosen_external_property: Bombieri-Vinogradov for actual Mangoldt AP prefixes
  final_known_power: old half-power fallback retained
  failed_strategy: normalized modulus averaging followed by independent progression-error norms
  exact_diagnosis: phi(q) classes reconstruct the principal source with coefficient one
  invariant_learned: nonprincipal zero-sum information cannot be spent after its coefficient has been cancelled by reconstruction
  forbidden_future_move: divide the AP error by Q while omitting phi(q), noncoprime powers or a continuum copy
  rollback: original finite centered source before artificial AP expansion
  reopen_trigger: independently proved nonvanishing source-weight coupling with a full smaller budget
  route_score: 2
  progress_class: NO_PROGRESS
  actual_route_impossibility: NOT_ESTABLISHED
  automatic_successor: NONE
```

### 10.3. Одно следующее действие

**CODEX DIRECTIVE — ограниченно проверить этот ввод-вывод, не запускать новый поиск по инерции.** Проверить (3.2), (4.1), коэффициент \(\varphi(q)\), всю поправку (3.4), minimax (5.2), dyadic/global цену (6.5) и точный главный компонент (7.2). Исполнить приложенные проверки. Приёмка означает **корректный отказ данного завершения как поставщика нужной степени**, не арифметический прогресс CCM. При дефекте вернуть первую неверную строку и исправленный бюджет. Нового вопроса, вычислительной кампании или автоматического Q30 эта директива не разрешает.

Репозиторий не изменялся. Lean, Arb, новый независимый reviewer и численный production-спектр не запускались.

## 11. Внешний первичный источник

**[W1]** R. C. Vaughan, *The Bombieri–Vinogradov Theorem*, авторский PDF, 25 страниц. Использованы определение \(\Lambda,\psi(x;q,a)\) (стр. 1), theorem statement (стр. 3) и его character context (стр. 2–4). Проверена ровно нужная unconditional формулировка с \(\max_b\sup_{y\le x}\). Полная независимая проверка доказательства теоремы не проводилась. Собственная totient-лемма (5.3) не заимствована из ошибочной поясняющей строки стр. 4.

```text
https://personal.science.psu.edu/rcv4/Bombieri.pdf
```

Математические преобразования §§3–9 — собственный вывод для указанного source map. Они отделены от внешней теоремы и от принятых источников S1–S9. Дополнительные предпосылки RH, GRH, ZF78, Mertens или сильной variance в этот вывод не вводились.


## Приложение A. Девять проверенных источников

| ID | Полное имя | Байты | LF тела | SHA-256 |
|---|---|---:|---:|---|
| S1 | `CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md` | 4681 | 93 | `9ca3dc230902ef9bbd097e21ebc07a32e7494aa76ef5f906f26e8f6a28a3f8a2` |
| S2 | `CCM_Q28_CONCLUSION.md` | 4256 | 77 | `6ae132365fe5ba4a5d96642b12591a7d9a743c8ddbd74076fec3f0b9adb12bf7` |
| S3 | `PROSHKA_CCM_ORIGINAL_P_SIGNED_RESIDUE_Q28_VERDICT_2026-10-26.md` | 90899 | 1282 | `770067a2a09efd146f18980a522d4de29bd4d924df0f39bf5273c3fc6f25e2f3` |
| S4 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 | 123 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` |
| S5 | `CCM_POST_Q25_SOURCE_PROPERTY_PREFLIGHT.md` | 2526 | 13 | `297a7fc170cfcb00a5cb4efde3ae593cc2bf1a6f913646e03f3d9c148e8cc0fc` |
| S6 | `CCM_Q20_SELBERG_PAIR_ATTEMPT.md` | 10197 | 190 | `4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f` |
| S7 | `CCM_Q15_VAUGHAN_JOINT_BUDGET.md` | 7127 | 139 | `1e13f0487d1a3362817e34112c11953a7296c18bd3500b31995aa221d540bf41` |
| S8 | `CCM_DIVISIBILITY_Q11_CONCLUSION.md` | 7455 | 94 | `465fdd818039eee8e27c1efc00f9659f2d96bef47fb0399b0e6554e09d5e76e5` |
| S9 | `PROSHKA_CCM_HIGH_ORDER_SIGNED_RETURN_Q10_VERDICT_2026-10-21.md` | 83808 | 1309 | `13d8f3a7bab5def121d04c3575018c50918e29ce8950aad80c6a82ce6c18db28` |

Размеры относятся к точным UTF-8 телам, без служебных BEGIN/END и одного разделительного LF. Встроенные исторические поручения — данные, не новые разрешения на действие. Все девять тел прочитаны, но все содержащиеся в них upstream-теоремы не пересертифицированы заново.

## Приложение B. Регистрация и исполняемые файлы

Ниже сохранены полные исходные файлы именно этого расчёта. Чтобы воспроизвести, сохрани каждый fenced-блок под именем из его заголовка в одной папке. Для математического проверяющего нужны Python 3 и SymPy; здесь использован SymPy 1.14.0, без установки новых зависимостей. Проверяющий байтов использует только стандартную библиотеку.

```bash
python3 check_q29.py
python3 verify_q29_sources.py /mnt/data/PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt
```

Во второй команде замени `/mnt/data/PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt` на **реальный путь к каноническому TXT на своей машине**, например `~/Downloads/PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt`. `registration.json` должен лежать рядом с `check_q29.py`. Скрипты пишут результаты рядом с собой. Никакой реконструкции производственной CCM или подстановки численного гипотетического нуля они не выполняют.

### FILE: registration.json

Bytes: 1304; SHA256: `eec752c5f6723e7d414d9bfc169a40a34c0d82c7462a58132227221023c0356b`.

```json
{
  "phase": "Q29",
  "stage": "All nine input bodies read; primary statement inspected; initial PAPER derivation completed; registration BEFORE new executable mathematical controls, not a blind discovery forecast",
  "chosen_mechanism": "Bombieri-Vinogradov progression-average transfer of the complete original-P centered matrix, retaining every reduced class and noncoprime prime power",
  "predictions": [
    {
      "id": "P1",
      "prediction": "Exact reconstruction uses the sum of all phi(q) reduced classes plus the omitted noncoprime prime-power correction; replacing their sum by their average is wrong."
    },
    {
      "id": "P2",
      "prediction": "For all normalized scalar modulus weights, the best l1-to-sum envelope has factor 1/sum(1/phi(q)), not 1/Q."
    },
    {
      "id": "P3",
      "prediction": "Before classwise moduli the nonprincipal components sum to zero; the original principal discrepancy survives with coefficient one."
    },
    {
      "id": "P4",
      "prediction": "The complete returned upper bound obtained this way has no new fixed-power saving and no proof of a source-pair coefficient margin."
    }
  ],
  "not_claimed": [
    "RH",
    "new prime theorem",
    "numerical actual CCM spectrum",
    "independent audit",
    "Lean",
    "Arb"
  ]
}
```

### FILE: check_q29.py

Bytes: 6274; SHA256: `af14abc8d9486c1fb6fe08052ad346d44c3f318aea9c398967ca9c4bfebf6e5f`.

```python
"""Exact local controls of the Q29 progression reconstruction.
Python 3 with SymPy. Run: python3 check_q29.py
These are finite algebra/provenance controls, not a CCM spectral certificate.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
from math import gcd
import json, hashlib, sys
import sympy as s

checks = Counter()
planted = []
def ck(value, group):
    if not bool(value):
        raise AssertionError(group)
    checks[group] += 1

def reject(name, wrong_equal):
    if bool(wrong_equal):
        raise AssertionError('Planted error was NOT detected: ' + name)
    planted.append(name)

def factors(n):
    out = {}; p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out

def mu(n):
    ff = factors(n)
    return 0 if any(k > 1 for k in ff.values()) else (-1)**len(ff)

def phi(n):
    out = n
    for p in factors(n): out = out//p*(p-1)
    return out

for n in range(1, 41):
    rhs = sum((F(mu(d)**2, phi(d)) for d in range(1,n+1) if n%d == 0), F(0))
    ck(rhs == F(n,phi(n)), 'totient_squarefree_identity')
reject('mu_instead_of_mu_squared',
       sum((F(mu(d),phi(d)) for d in (1,2)), F(0)) == F(2,phi(2)))

# This controls the exact minimax algebra, not an asymptotic prime error.
for Q in (1,2,3,5,8,12,20):
    S = sum((F(1,phi(q)) for q in range(1,Q+1)), F(0))
    beta = [F(1,phi(q))/S for q in range(1,Q+1)]
    ck(sum(beta) == 1, 'optimal_weights_normalized')
    ck(set(beta[q-1]*phi(q) for q in range(1,Q+1)) == {1/S},
       'minimax_equalized_coefficients')
    for j in range(1,Q+1):
        # An l1-budget concentrated at j attains the corresponding coefficient.
        D = [F(int(q==j)) for q in range(1,Q+1)]
        ck(sum(beta[q-1]*phi(q)*D[q-1] for q in range(1,Q+1)) == 1/S,
           'dual_l1_extreme_point')

# Formal log(p) symbols keep the ACTUAL Mangoldt support and multiplicities.
logs = {p:s.Symbol('logp_'+str(p), real=True) for p in range(2,66) if len(factors(p))==1 and factors(p).get(p)==1}
def Lam(n):
    ff=factors(n)
    return logs[next(iter(ff))] if len(ff)==1 else s.S(0)
x = s.Symbol('x', real=True)
H = s.Matrix([[x+1, 1+s.I*x], [1-s.I*x, x*x+2]])
def HH(n): return H.subs(x,n)
def zero(A): return all(s.expand(z)==0 for z in A)
def integral_H(a,b): return H.applyfunc(lambda e:s.integrate(e,(x,a,b)))
def msum(terms):
    z=s.zeros(2)
    for term in terms: z += term
    return z

saved = None
for X,Y in ((4,8),(8,13),(16,32)):
    J = integral_H(X,Y)
    full = msum(Lam(n)*HH(n) for n in range(X+1,Y+1)) - J
    for q in (1,2,3,4,6):
        units=[a for a in range(1,q+1) if gcd(a,q)==1]
        cop=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if gcd(n,q)==1)
        bad=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if gcd(n,q)>1)
        Ds=[]; Zs=[]
        for a in units:
            cls=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if (n-a)%q==0)
            D=cls-J/phi(q)
            Z=cls-cop/phi(q)
            Ds.append(D);Zs.append(Z)
            ck(zero(D-Z-(full-bad)/phi(q)), 'actual_principal_channel_identity')
        ck(zero(msum(Ds)+bad-full), 'full_matrix_residue_reassembly')
        ck(zero(msum(Zs)), 'nonprincipal_zero_sum_before_moduli')
        # Check the omitted atoms as prime powers, not a scalar norm surrogate.
        bad2=s.zeros(2)
        for p in factors(q):
            n=p
            while n<=Y:
                if n>X: bad2 += logs[p]*HH(n)
                n*=p
        ck(zero(bad-bad2), 'all_noncoprime_prime_powers_retained')
        if (X,Y,q)==(4,8,3): saved=(full,J,cop,bad,Ds)
        if (X,Y,q)==(4,8,2):
            reject('deleted_noncoprime_power_8',zero(msum(Ds)-full))

full,J,cop,bad,Ds=saved
reject('average_classes_instead_of_sum',zero(msum(Ds)/2+bad-full))
reject('full_continuum_subtracted_in_each_class',zero(cop-2*J+bad-full))
reject('deleted_off_diagonal_mixed_entries',zero(s.diag(full[0,0],full[1,1])-full))

# An exact Stieltjes test with the actual formal Mangoldt atoms. Integrate the
# step function E on each unit interval; the matrix weight here is an algebra
# control only, not production Q_M(log x)/sqrt(x).
X,Y,q,a=4,13,3,1
E=lambda n: sum((Lam(k) for k in range(1,n+1) if (k-a)%q==0),s.S(0))-s.Rational(n,phi(q))
D=msum(Lam(n)*HH(n) for n in range(X+1,Y+1) if (n-a)%q==0)-integral_H(X,Y)/phi(q)
Hp=H.diff(x); integ=s.zeros(2)
for n in range(X,Y):
    ps=sum((Lam(k) for k in range(1,n+1) if (k-a)%q==0),s.S(0))
    integ += (Hp*(ps-x/phi(q))).applyfunc(lambda e:s.integrate(e,(x,n,n+1)))
right=HH(Y)*E(Y)-HH(X)*E(X)-integ
ck(zero(D-right),'stieltjes_full_both_endpoints')
reject('deleted_lower_Stieltjes_endpoint',zero(D-(HH(Y)*E(Y)-integ)))

for p in (2,3,5,7):
    for X in (1,2,4,8,16,32):
        ns=[];n=p
        while n<=2*X:
            if n>X:ns.append(n)
            n*=p
        ck(len(ns)<=1,'one_power_per_prime_in_open_closed_dyadic_block')

O,r=s.symbols('O r',real=True)
variation=2/r+2+2*(1+2*O)*(1-1/r)
ck(s.expand(variation-(4*(1+O)-4*O/r))==0,'matrix_variation_price_algebra')
for eps in (F(1,64),F(1,128),F(1,257)):
    ck(F(1,2)+eps > F(1,2), 'completed_BV_power_not_better_than_half')
    ck(F(3,2)*eps < F(1,2), 'short_divisor_fee_not_the_dominant_debt')
    ck(-eps < 0, 'summed_noncoprime_return_decays')

base=Path(__file__).resolve().parent
out={
 'status':'PASS_EXACT_LOCAL_CONTROLS',
 'exact_controls':sum(checks.values()),
 'counts':dict(checks),
 'planted_errors_detected':len(planted),
 'planted_names':planted,
 'scope':'Finite coefficient, matrix, endpoint and minimax algebra. The test matrix is Hermitian with complex off-diagonal entries but is NOT a production CCM cell. Formal log(p) retains actual Mangoldt support. No infinite prime estimate is proved by these controls.',
 'python':sys.version.split()[0], 'sympy':s.__version__,
 'lean_runs':0, 'arb_runs':0, 'production_spectral_runs':0,
 'new_independent_review':'NOT_RUN',
 'registration_sha256':hashlib.sha256((base/'registration.json').read_bytes()).hexdigest(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
(base/'exact_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
```

### FILE: exact_results.json

Bytes: 1593; SHA256: `578b9018493e1db17a9a5c531d708d22c279fb09d64d78e30175d1be96bfd56e`.

```json
{
  "status": "PASS_EXACT_LOCAL_CONTROLS",
  "exact_controls": 209,
  "counts": {
    "totient_squarefree_identity": 40,
    "optimal_weights_normalized": 7,
    "minimax_equalized_coefficients": 7,
    "dual_l1_extreme_point": 51,
    "actual_principal_channel_identity": 24,
    "full_matrix_residue_reassembly": 15,
    "nonprincipal_zero_sum_before_moduli": 15,
    "all_noncoprime_prime_powers_retained": 15,
    "stieltjes_full_both_endpoints": 1,
    "one_power_per_prime_in_open_closed_dyadic_block": 24,
    "matrix_variation_price_algebra": 1,
    "completed_BV_power_not_better_than_half": 3,
    "short_divisor_fee_not_the_dominant_debt": 3,
    "summed_noncoprime_return_decays": 3
  },
  "planted_errors_detected": 6,
  "planted_names": [
    "mu_instead_of_mu_squared",
    "deleted_noncoprime_power_8",
    "average_classes_instead_of_sum",
    "full_continuum_subtracted_in_each_class",
    "deleted_off_diagonal_mixed_entries",
    "deleted_lower_Stieltjes_endpoint"
  ],
  "scope": "Finite coefficient, matrix, endpoint and minimax algebra. The test matrix is Hermitian with complex off-diagonal entries but is NOT a production CCM cell. Formal log(p) retains actual Mangoldt support. No infinite prime estimate is proved by these controls.",
  "python": "3.13.5",
  "sympy": "1.14.0",
  "lean_runs": 0,
  "arb_runs": 0,
  "production_spectral_runs": 0,
  "new_independent_review": "NOT_RUN",
  "registration_sha256": "eec752c5f6723e7d414d9bfc169a40a34c0d82c7462a58132227221023c0356b",
  "script_sha256": "af14abc8d9486c1fb6fe08052ad346d44c3f318aea9c398967ca9c4bfebf6e5f"
}
```

### FILE: verify_q29_sources.py

Bytes: 1915; SHA256: `789da22d8ec62575c638eaf41d1ef0b636e623f2df977ea60ceabe25b6707ec3`.

```python
"""Verify the exact Q29 attachment and all nine byte-locked source bodies.
Run: python3 verify_q29_sources.py /path/to/PROSHKA_CCM_ACTUAL_SOURCE_ROLLBACK_Q29_2026-10-26.txt
The argument is the actual local path to the attached canonical TXT.
"""
from pathlib import Path
import hashlib, json, re, sys

EXPECTED=(223966,3385,'652b6f8fd2c4b90eb06101fc8bfa0b85f96062c2ee06a9208fdde71f98d97f2e')
if len(sys.argv)!=2:
    raise SystemExit('Usage: python3 verify_q29_sources.py CANONICAL_Q29_TXT')
p=Path(sys.argv[1]); raw=p.read_bytes(); raw.decode('utf-8')
observed=(len(raw),raw.count(b'\n'),hashlib.sha256(raw).hexdigest())
if observed!=EXPECTED: raise SystemExit('Canonical request mismatch: '+repr(observed))
header=raw.split(b'BEGIN SOURCE S1:',1)[0].decode('utf-8')
rows=re.findall(r'^(S\d+): ([^;\n]+); bytes=(\d+); sha256=([0-9a-f]{64})$',header,re.M)
if len(rows)!=9:raise SystemExit('Expected nine manifest entries')
results=[]
for sid,name,n,sha in rows:
    marker=('BEGIN SOURCE '+sid+': '+name+'\n').encode('utf-8')
    if raw.count(marker)!=1:raise SystemExit('Nonunique source marker: '+sid)
    start=raw.index(marker)+len(marker); n=int(n); body=raw[start:start+n]
    if hashlib.sha256(body).hexdigest()!=sha:raise SystemExit('Source hash mismatch: '+sid)
    if not raw[start+n:].startswith(('\nEND SOURCE '+sid).encode('utf-8')):
        raise SystemExit('Source end/separator mismatch: '+sid)
    body.decode('utf-8')
    results.append({'id':sid,'name':name,'bytes':n,'lf':body.count(b'\n'),'sha256':sha})
out={'status':'PASS_BYTE_LOCKS','request_bytes':observed[0],'request_lf':observed[1],
     'request_sha256':observed[2],'sources':results,
     'scope':'Provenance only. Does not independently verify mathematical source claims.'}
Path(__file__).with_name('source_results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
```

### FILE: source_results.json

Bytes: 2169; SHA256: `da8be87885766a3f08f3f9a17eb4349632f0b96a49d6088211246dd99610367e`.

```json
{
  "status": "PASS_BYTE_LOCKS",
  "request_bytes": 223966,
  "request_lf": 3385,
  "request_sha256": "652b6f8fd2c4b90eb06101fc8bfa0b85f96062c2ee06a9208fdde71f98d97f2e",
  "sources": [
    {
      "id": "S1",
      "name": "CCM_POST_Q28_EULER_POSITIVITY_PREFLIGHT.md",
      "bytes": 4681,
      "lf": 93,
      "sha256": "9ca3dc230902ef9bbd097e21ebc07a32e7494aa76ef5f906f26e8f6a28a3f8a2"
    },
    {
      "id": "S2",
      "name": "CCM_Q28_CONCLUSION.md",
      "bytes": 4256,
      "lf": 77,
      "sha256": "6ae132365fe5ba4a5d96642b12591a7d9a743c8ddbd74076fec3f0b9adb12bf7"
    },
    {
      "id": "S3",
      "name": "PROSHKA_CCM_ORIGINAL_P_SIGNED_RESIDUE_Q28_VERDICT_2026-10-26.md",
      "bytes": 90899,
      "lf": 1282,
      "sha256": "770067a2a09efd146f18980a522d4de29bd4d924df0f39bf5273c3fc6f25e2f3"
    },
    {
      "id": "S4",
      "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
      "bytes": 5633,
      "lf": 123,
      "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2"
    },
    {
      "id": "S5",
      "name": "CCM_POST_Q25_SOURCE_PROPERTY_PREFLIGHT.md",
      "bytes": 2526,
      "lf": 13,
      "sha256": "297a7fc170cfcb00a5cb4efde3ae593cc2bf1a6f913646e03f3d9c148e8cc0fc"
    },
    {
      "id": "S6",
      "name": "CCM_Q20_SELBERG_PAIR_ATTEMPT.md",
      "bytes": 10197,
      "lf": 190,
      "sha256": "4e4ea8dd3107c7ce9bd1e3d829bc46dfc3406b2f61153bf06a33bd69e3cd977f"
    },
    {
      "id": "S7",
      "name": "CCM_Q15_VAUGHAN_JOINT_BUDGET.md",
      "bytes": 7127,
      "lf": 139,
      "sha256": "1e13f0487d1a3362817e34112c11953a7296c18bd3500b31995aa221d540bf41"
    },
    {
      "id": "S8",
      "name": "CCM_DIVISIBILITY_Q11_CONCLUSION.md",
      "bytes": 7455,
      "lf": 94,
      "sha256": "465fdd818039eee8e27c1efc00f9659f2d96bef47fb0399b0e6554e09d5e76e5"
    },
    {
      "id": "S9",
      "name": "PROSHKA_CCM_HIGH_ORDER_SIGNED_RETURN_Q10_VERDICT_2026-10-21.md",
      "bytes": 83808,
      "lf": 1309,
      "sha256": "13d8f3a7bab5def121d04c3575018c50918e29ce8950aad80c6a82ce6c18db28"
    }
  ],
  "scope": "Provenance only. Does not independently verify mathematical source claims."
}
```

### FILE: external_source.json

Bytes: 252; SHA256: `62acfd8391c0dc398cae46f559ae22eb9d4bbacc31dcfa3163fc73899d22adb3`.

```json
{
  "url": "https://personal.science.psu.edu/rcv4/Bombieri.pdf",
  "status": "RAW_DOWNLOAD_FAILED",
  "reason": "<urlopen error [Errno -3] Temporary failure in name resolution>",
  "used": "Web parsed PDF and screenshots pp3-4; no raw hash claimed."
}
```

## Заключительная граница

**Теорема о прогрессиях применена в законной области к настоящим коэффициентам; её полный матричный возврат не улучшает исходную степень.** Оптимальный логарифмический коэффициент реконструкции, дешёвый сектор исключённых простых степеней и выполненные проверки не засчитываются как выигрыш CCM. Первая непоставленная знаковая оценка осталась у полного главного источника. Новая благоприятная степень, коэффициентный зазор, SP, G1/G3 и RH в этом ответе не доказаны.
