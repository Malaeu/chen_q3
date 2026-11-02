# STATUS: TRY_FIXED_BACKGROUND_SECOND_MOMENT
```yaml
OPERATIVE_CLASS: TRY_FIXED_BACKGROUND_SECOND_MOMENT
DATE: 2026-11-01
AUTHORITY: DIRECT_OWNER_REQUEST_FOR_NEXT_RESEARCH_STEP
SOURCE_COMMIT: ae344193b74c1394129b5fc6053342b620761f3c
SOURCE_BRANCH: proshka_inbox_2026-10-31
ARTIFACT_KIND: RESEARCH_DECISION_AND_SINGLE_NEXT_TARGET
RESULT: STRATEGY_SELECTED_NOT_AN_ARITHMETIC_PROOF
TARGET_SECOND_MOMENT_BOUND: NOT_PROVED
BACKGROUND_CONSUMER: INHERITED_PAPER_NOT_INDEPENDENTLY_AUDITED
MUK_USED_AS_PREMISE: false
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
NEW_ALGEBRA_CHECKS: 2
INDEPENDENT_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 1. Решение и основания

Выбран следующий ограниченный исследовательский ход: проверить равномерный **второй момент точного усреднённого символа на одном фиксированном theta-фоне h**, сохранив совместную компенсацию простых степеней и непрерывного главного члена. Это выбранная попытка, не доказанная оценка. Второй момент — достаточный интерфейс, не обязательное усиление цели.

Прочитанные источники на SOURCE_COMMIT:

- S1: `docs/routeB_bus/proshka/PROSHKA_VERDICT_MUK_2026-11-01.md`, §§0–2 и начало §3, blob `5391bc46c3e39a57739dc6650d9ca6f6f0c92e59`. PAPER-кандидат mu_K <= C_* log^4(2K); независимый аудит не заявлен.
- S2: `docs/routeB_bus/proshka/PROSHKA_VERDICT_NEGATIVE_LEAKAGE_2026-11-01.md`, определения, исходниковая нулевая формула, §4 и §6, blob `f9675380ad1d48d338b4bf65bc6011d3620c8542`. Критерий фиксированного фона наследуется на PAPER-уровне; нового полного аудита нет.
- S3: HARDBREAK, commit `2258f6b02aad1e3c8cd073a7e1ecb80dbfbef2e1`, Lemma 7: используется доступная конструкция нуль-возмущения и её разбор в S2, без нового полного чтения HARDBREAK.
- Protocol: `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` получен через GitHub с rh_clean, включая конец.
- E1: Erdélyi–Szabados, *On a generalization of the Bernstein–Markov inequality*, авторский PDF `https://people.tamu.edu/~terdelyi/papers-online/bernstein02.pdf`, Theorem 1 (2.1), Lemma 1 (2.3). Первичный текст подтверждает формулировку специального импорта MUK. Это не аудит всего приложения к H. Попытка web-screenshot p.5 вернула Cache miss; визуальная проверка не заявляется.

Новые quasi-RH предпосылки не используются. Рост M^(5/12+epsilon) не считается равномерной константой.

## 2. Потребитель и выбранная оценка

**[COFINAL_FAMILY | CONDITIONAL; на корректности S2, Theorem 6.]** При
\[
H(t)=4\xi(1/2-it),\quad p_h(t)=|H(t)|^2/(2\pi),\quad
G_h=\mathscr G[h]=\int w(t)p_h(t)dt>0
\]
S2 утверждает: ограниченность
\[
\mathcal N_j(h)=G_h^{-1}\int p_h(t)(-\overline B_j(t))_+dt
\]
на поздней неограниченной подпоследовательности положительных средних исходных масштабов эквивалентна RH. Требуется независимая проверка этого перехода: fixed-profile convergence, поляризация, плотность тестов в C_0, полная вариация и отрицательный тест по невещественной четвёрке.

Фиксируем s0=log 2, целое M>=3 и
\[
q_M(s)=\frac1{M+1}\sum_{m=M}^{2M}(1-s/\log m)_+,
\quad d\nu(s)=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)-e^{s/2}ds,
\]
\[
\overline B_M(t)=2\int_{(s_0,\infty)}q_M(s)\cos(ts)d\nu(s).
\]
Это вспомогательное среднее, не изменение CCM N=m, L=log m.

**Следующая недоказанная source-оценка:**
\[
\boxed{\exists C_2<\infty\ \exists M_j\to\infty:\quad
\mathcal V_{M_j}:=G_h^{-1}\int p_h(t)\overline B_{M_j}(t)^2dt\le C_2.}
\tag{T}
\]

**[ABSTRACT | PAPER; элементарный переход.]** Cauchy–Schwarz даёт
\[
\mathcal N_M(h)\le\frac{\|h\|_2}{\sqrt{G_h}}\sqrt{\mathcal V_M}.
\tag{1}
\]
Следовательно, (T) плюс независимо проверенный потребитель S2 доказывают RH. Растущие jets, точечные пики и mu_K здесь не являются обязательными предпосылками. MUK сохраняется как инструмент резервной detector-линии.

## 3. Точная двойная арифметическая корреляция

**[FINITE_CELL | PAPER; тождество, не оценка.]** Пусть
\(Q_h(v)=2\int h(x)h(x+v)dx\). Тогда
\[
\boxed{G_h\mathcal V_M=
\iint q_M(s)q_M(u)[Q_h(s-u)+Q_h(s+u)]d\nu(s)d\nu(u),}
\tag{2}
\]
где обе переменные лежат в (s0,infinity).

Проверка: \(\int p_h\cos(vt)=Q_h(v)/2\), поэтому
\(4\int p_h\cos(st)\cos(ut)=Q_h(s-u)+Q_h(s+u)\).
При конечном M мера q_M dnu имеет конечную полную вариацию и компактную поддержку, так что Fubini законен.

В (2) остаются четыре совместных вклада:
\[
\nu_p\otimes\nu_p-\nu_p\otimes\nu_c-\nu_c\otimes\nu_p+\nu_c\otimes\nu_c.
\]
Первый содержит буквальные \(\Lambda(n)\Lambda(k)/\sqrt{nk}\) и ядра
\(Q_h(\log(n/k))\), \(Q_h(\log(nk))\).
Диагональ n=k, оба mixed-члена, все proper powers, near-граница и верхние атомы сохраняются. Интеграл по t идёт по всей прямой.

Оценивать надо полное компенсированное спаривание (2). Отдельные растущие мажоранты четырёх частей не засчитываются как отмена. Это НЕ ранее запрещённая carrier-wide оценка ||Z_m||: здесь один фиксированный фон и другой функционал.

## 4. Дискриминатор против нуль-возмущения

**[ABSTRACT | PAPER; диагностическая алгебра.]** Если символ меняется на B+A D, где \(\int p_hD=0\), но D не тождественно нулевая, то
\[
\mathcal V_M(A)=\mathcal V_M(0)
+\frac{2A}{G_h}\int p_hBD
+\frac{A^2}{G_h}\int p_hD^2.
\tag{3}
\]
Последний коэффициент строго положителен: p_h>0 почти всюду и непрерывная D ненулевая. Поэтому возмущение, невидимое для линейных средних конечного джета, видно во втором моменте. Для фиксированного M при A→infinity он растёт квадратично.

Это не доказывает (T) для настоящего источника и не запрещает A-зависимую константу для фиксированного A. Необходимая арифметическая связь остаётся
\[
\int_0^\infty e^{-zs}d\nu(s)
=-\zeta'/\zeta(z+1/2)-1/(z-1/2),\quad\Re z>1/2.
\]
Добавка b(s)ds меняет её на ненулевую целую Laplace-функцию. Доказательство должно использовать точный источник сверх конечных моментов и показать, где новый член меняет бюджет. Само это тождество ещё не является upper-bound.

## 5. Проверки, риск и два допустимых представления

Исполнены две SymPy-проверки: тригонометрический множитель в (2) и квадрат в (3). Они не проверяют source-bound, аналитические импорты или независимость аудита.

Предсказания перед будущим тестом:
P1: второй момент совместим с условной RH-ветвью; здесь НЕ ПРОВЕРЕНО. Нужно проверить реальные Fejer-пики с H^2, без разделённости нулей. RH в этой проверке разрешена только как проверка силы цели, не как предпосылка (T).
P2: раздельные absolute-budgets теряют полезную компенсацию; здесь прогноз, не запрет всех возможных разложений.
P3: нуль-возмущение имеет положительный квадратичный коэффициент в (3); проверено алгеброй.

Сильнейшее возражение: второй момент сильнее минимально достаточной отрицательной L1-массы. Поэтому он не объявлен необходимым. Если цена усиления не проходит контроль, вернуться к прямому Jordan-bound, не объявляя RH-маршрут мёртвым.

| Представление | Потенциальная сила / цена | Дискриминатор |
|---|---|---|
| Выбранный двойной compensated moment | Высокая / высокая арифметическая, низкая алгебраическая | Диагональ и две cross-компенсации; видимость (3) |
| Прямой Jordan-upper на h | Минимальная достаточная цель / сложная нелинейность | Source-majorant без удаления невещественного нулевого остатка |

Vanishing identity имеется для линейных радикальных средних, но не обнуляет (2). Ни одной новой source-константы этим выбором не доказано.

## 6. Единственная CODEX DIRECTIVE

**AUDIT_AND_TEST_FIXED_BACKGROUND_COMPENSATED_SECOND_MOMENT**

Сначала отдельный read-only reviewer проверяет S2, Theorem 6; текущий ответ не является независимой проверкой. Затем выполнить одну source-попытку (T) через (2). Самый дешёвый предварительный тест — совместимость второго момента с RH-ветвью; RH не импортировать в основную оценку.

Сохранить диагональ, оба mixed-вклада, continuum-square, prime powers, окна и весь частотный хвост. Получить actual C_2 независимо от M на неограниченной последовательности либо указать первый конкретный неоплаченный совместный член. Не ограничиваться ещё одной эквивалентной формулировкой.

Запреты: занулить возможные невещественные нули; использовать только конечные точные моменты; предположить независимость простых; удалить n=k; заменить цель полным ||Z_m||; принять численную стабилизацию за квантор; считать MUK доказательством (T).

Успех: `BACKGROUND_SECOND_MOMENT_SOURCE_BOUND` с константой и остатками.
Неуспех попытки: `BACKGROUND_SECOND_MOMENT_FIRST_UNPAID_PAIRING` с точным членом.
Чрезмерное усиление цели: `SECOND_MOMENT_INTERFACE_REJECTED`, без отказа от direct-L1/RH маршрута.

## 7. Consumer-first ledger и closeout

**[ABSTRACT | CONDITIONAL; стратегический выбор.]**
DOWNSTREAM_CONSUMER: RH через S2 после независимой проверки.
ACTUAL_CONSUMER_REQUIREMENT: bounded negative h-mass.
ORIGINAL_OBJECT_IS: second-moment NOT_PROVED_NECESSARY.
KNOWN_WEAKER_INTERFACES: direct negative-L1; (T) => нужный bound по (1).
FAILURE_TYPE: NO_DERIVATION для (T).
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: FIXED_BACKGROUND_DOUBLE_SOURCE_CORRELATION.
REOPEN_TRIGGER: реальный upper для (2) или более дешёвый Jordan-majorant.
DISCRIMINATOR: нелинейная масса должна видеть source-возмущение.

Следующий шаг получил один явный объект. Не получены арифметическая верхняя константа, независимый аудит или RH. Выбор стратегии не выдаётся за proof-progress. Память: фиксированный h и двойная компенсация вместо обязательного роста джета; direct-L1 остаётся резервом.
