# STATUS: TRY_FULL_PRIME_CORE_DIRECT

```yaml
OPERATIVE_CLASS: TRY_FULL_PRIME_CORE_DIRECT
DATE: 2026-11-04
AUTHORITY: DIRECT_OWNER_REQUEST_TO_PROVE_THE_RH_CLOSING_STATEMENT
FORMAL_TXT_BUS_ADJUDICATION: NOT_PERFORMED
ROUTE: CHALLENGER_NOT_RH
RH_PROVED: false
CORE_PROVED: false
CORE_IS_RH_EQUIVALENT: true
CORE: PRIME_ONLY_UPPER_BOUND_ON_POLE_NULL_AND_MEAN_ZERO_SUBSPACE
SOURCE_COMMIT: 115714b718a6a7299121d0716d954b081aca5ff9
SOURCE_BLOB: 9feeb0571aff5d79c2617694e9ef31f4d9f1a121
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
WRITE_BRANCH: proshka_inbox_2026-10-31
WRITE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_FULL_PRIME_CORE_DIRECT_2026-11-04.md
KILLS: []
NEW_SIGN_SUPPLIER: NONE
NEW_THEOREM_CLAIMED: false
PROGRESS_CLASS: NO_PROGRESS
RH_SIGN_PROGRESS: NONE
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 2
MINIMAL_MISSING_IDENTITY: "exists C>=0 and integers m_k->infinity: z*B_mk^(1)z <= C z*(I+X_mk)z for every k and every z with z0=0 and p_mk*z=0"
UNRESOLVED_DIRECT_STEP: UNIFORM_ONE_SIDED_BOUND_FOR_COMPLETE_SIGNED_THETA_ERROR_PAIRING
VERIFIER: PAPER
SCOPE: [ABSTRACT, FINITE_CELL, COFINAL_FAMILY]
NUMERICAL_TESTS: NOT_RUN
SYMBOLIC_COMPUTATIONAL_TESTS: NOT_RUN
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
INDEPENDENT_ANALYTIC_AUDIT: NOT_PERFORMED
ROUTE_STATE_CHANGED: false
COMMIT_SHA: REPORTED_AFTER_REMOTE_WRITE
```

Ы. **Нужно доказать (T) ниже. Её доказательство завершило бы имеющуюся цепочку до RH. В этой попытке (T) не доказана.** Прямое оценивание всей формы выполнено без разбиения на независимые диапазоны, но полученный коэффициент растёт с окном. Это не новый знак, не опровержение (T) и не новый результат о RH. Отдельные запреты и уже известные тождества не заменяют недостающую верхнюю оценку.

## 0. Источники и статус

[FINITE_CELL / COFINAL_FAMILY | PAPER; наследование, не новый независимый аудит.]

R1. `docs/routeB_bus/proshka/PROSHKA_VERDICT_PRIME_POWER_RANK_ONE_2026-11-04.md`, commit `115714b718a6a7299121d0716d954b081aca5ff9`, blob `9feeb0571aff5d79c2617694e9ef31f4d9f1a121`. Через GitHub перечитаны Теорема 2, точный возврат ограничений, доказательство эквивалентности и полный остаток §4. Используются также явно названные там унаследованные Gamma-оценка, смешанная радикальность и отрицательный свидетель при not-RH. Эти более ранние зависимости здесь заново не переаудированы.

R2. `PROSHKA_VERDICT_PRIME_ADJACENT_SHELLS_2026-11-04.md`, commit `603b24e180a35f7b7139881318ae4e305bd9bd58`, remote blob из предыдущей доставки `0d4620e6e2b40ab23c526319b5ec37762a8c6bf3`. Смонтированный текст просмотрен для ограничения scope: он запрещает самостоятельные бюджеты необработанных диапазонов, но не доказывает (T). Его теорема не используется как посылка нового знака.

T1 — **THEOREM**, количественная PNT. Достаточно существования фиксированного H с

\[
|\vartheta(x)-x|\le H\frac{x}{(1+\log x)^4}\quad(x\ge1).
\]

Это следствие классической оценки ошибки PNT. Проверены NIST DLMF §27.12, (27.12.5), и авторский abstract Johnston–Yang, arXiv:2204.01980v2. Численный onset, проверка нулей до конечной высоты и RH-остаток не используются. Из оценки для pi к theta переходят частичным суммированием; из оценки для psi — вычитанием O(sqrt(x) log²x) собственных степеней. Конечный начальный диапазон поглощается увеличением H.

```text
https://dlmf.nist.gov/27.12.E5
https://arxiv.org/abs/2204.01980v2
```

Новых внешних теорем, которые давали бы нужный совместный знак, не найдено и не импортировано. Это не утверждение о невозможности такого доказательства.

## 1. Единственная цель, без смены объекта

[COFINAL_FAMILY | CONDITIONAL: целевое утверждение ОТКРЫТО.]

m — целое >=3, L=log m, I_L=(-L/2,L/2). Буквальные физически ортонормированные косинусы:

\[
\phi_j(x)=d_j(-1)^jL^{-1/2}\cos(\omega_jx),\qquad
\omega_j=2\pi j/L,\quad d_0=1,\quad d_j=\sqrt2\ (j>0),\quad 0\le j\le m.
\]

Пусть f=S_m z, X_m=diag(omega_j²), G_m=I+X_m. За окном используется нулевое продолжение; в graph-норме производные внутренние:

\[
z^*G_mz=\|f\|_2^2+\|f'_{\rm int}\|_2^2=:\mathcal E_m(f).
\]

R_s — исходный двусторонний обрезанный сдвиг после сжатия; это не периодический сдвиг. Определим

\[
B_m^{(1)}=\sum_{p<m}\frac{\log p}{\sqrt p}R_{\log p},\qquad
p_m=S_m^*(\sqrt2\cosh(x/2)),\qquad
\mathcal K_m=\{z:z_0=0,\ p_m^*z=0\}.
\]

Нужно доказать ровно

\[
\boxed{\exists C\ge0\ \exists(m_k)_{k\ge1}\subset\mathbb N,
\quad m_k\to\infty:\quad
z^*B_{m_k}^{(1)}z\le C z^*G_{m_k}z
\quad\forall k\ \forall z\in\mathcal K_{m_k}.} \tag{T}
\]

Одна и та же C должна работать для всех векторов и всех выбранных окон. Нельзя переставить кванторы и разрешить C зависеть от z или k. Последовательность окон может быть любой неограниченной; точный PSD каждого A_m, исчезающий бюджет и оценка на отдельные диапазоны простых не требуются.

## 2. Почему (T) действительно завершает цепочку

[COFINAL_FAMILY | PAPER; сокращённый повтор унаследованной импликации R1, не новое доказательство (T).]

Из R1 известно, с одной конечной K:

\[
-KG_m\preceq B_m^{(\ge2)}-(L/2)e_0e_0^*\preceq KG_m.
\]

На K_m этот ранг равен нулю, как и полюс. Поэтому из (T), A_m=H_m+p_mp_m^*-B_m и H_m>=-c_*I следовало бы

\[
z^*A_{m_k}z\ge-(c_*+C+K)z^*G_{m_k}z\quad(z\in\mathcal K_{m_k}). \tag{2.1}
\]

R1 возвращает каждый фиксированный чётный гладкий экспоненциально убывающий f с hat f(0)=hat f(i/2)=0 в эти же конечные пространства, с точными двумя ограничениями. После k->infinity (2.1) даёт

\[
W[f]\ge-C_*\|f\|_{H^1}^2. \tag{2.2}
\]

Радикальные функции с Fourier-образами

\[
t^2(t^2+1/4)\Xi(t)e^{-t^2}\cos(at)
\]

имеют те же два нулевых момента, смешанно спариваются в нуль с полной W и плотны в чётном H¹. Для каждого фиксированного f выбираем h_n из их линейной оболочки с h_n->f в H¹. Тогда

\[
W[f]=W[f-h_n]\ge-C_*\|f-h_n\|_{H^1}^2\longrightarrow0. \tag{2.3}
\]

Два момента снимаются радикальными поправками из R1; получается W>=0 на полном исходном классе. Отрицательный источник-свидетель для любого внелинейного нуля исключает такой нуль. Это завершило бы RH.

Обратно, RH даёт A_m>=0; на K_m имеем B_m^(1)<=H_m-B_m^(>=2)<=(16+K)G_m. Поэтому (T) действительно RH-эквивалентна в принятом PAPER-пакете. В этой записи RH не взята как предпосылка прямого направления.

## 3. Прямая попытка для всей суммы

[FINITE_CELL / COFINAL_FAMILY | PAPER: точные тождества и вывод имеющегося бюджета; требуемая постоянная оценка не получена.]

Для f=S_m z, z∈K_m положим N=||f||², D=||f'_int||² и

\[
Q_f(s)=2\Re\int_{-L/2}^{L/2-s}\overline{f(x)}f(x+s)\,dx.
\]

Имеем Q_f(0)=2N, Q_f(L)=0. Полный край сохраняется:

\[
Q_f'(s)=2\Re\int_{-L/2}^{L/2-s}\overline{f(x)}f'(x+s)\,dx
-2\Re\bigl(\overline{f(L/2-s)}f(L/2)\bigr).
\]

Из R1, либо из оценки ||f||_infty²<=N/L+2sqrt(ND), следуют

\[
|Q_f(s)|\le2N,\qquad |Q_f'(s)|\le5(N+D),\quad L\ge1. \tag{3.1}
\]

Введём

\[
D_\vartheta(s)=e^{-s/2}\bigl(\vartheta(e^s)-e^s\bigr),\quad
J_-[f]=\int_0^L e^{-s/2}Q_f(s)\,ds,
\]

\[
\mathcal R_m[f]=\int_0^L D_\vartheta(s)
\left(\tfrac12Q_f(s)-Q_f'(s)\right)\,ds. \tag{3.2}
\]

**Вся сумма одновременно**, с точными endpoints, равна

\[
\boxed{z^*B_m^{(1)}z=2N-J_-[f]+\mathcal R_m[f].} \tag{3.3}
\]

Вывод: записать исходную сумму как интеграл t^(-1/2)Q_f(log t) по dtheta(t), отделить dt и проинтегрировать остаток по частям. В t=m вес равен нулю; в t=1 значение theta(1)-1=-1 даёт +2N. На p_m-perp полюсное тождество даёт integral e^(s/2)Q_f(s)ds=-J_-[f]. Положительный Fourier-множитель ядра e^(-|x-y|/2), равный 1/(t²+1/4), даёт

\[
0\le J_-[f]\le4N. \tag{3.4}
\]

Ни простой атом, ни промежуточная граница не выброшены. Это уже известное представление R1, применённое к совместной цели, а не новая арифметическая теорема.

Из (3.3)–(3.4) цель (T) эквивалентна существованию такого же типа постоянной верхней оценки

\[
\boxed{\mathcal R_{m_k}[S_{m_k}z]\le C_R z^*G_{m_k}z
\quad(k\ge1,\ z\in\mathcal K_{m_k}).} \tag{R}
\]

В обе стороны достаточно увеличить соответствующую константу на 2. Это проверка точного места незакрытого перехода, не новое RH-сведение, засчитанное за прогресс.

## 4. Где прямое оценивание остановилось

[COFINAL_FAMILY | PAPER; недостаточность выполненной оценки, не отрицание (T) или (R).]

T1 и (3.1) дают для всех исходных m>=3 и всех z∈K_m:

\[
|\mathcal R_m[f]|\le6H\mathcal E_m(f)
\int_0^L\frac{e^{s/2}}{(1+s)^4}\,ds. \tag{4.1}
\]

Обозначим интеграл A(L). Он удовлетворяет

\[
A(L)\sim\frac{2e^{L/2}}{(1+L)^4}\longrightarrow\infty. \tag{4.2}
\]

Например, (4.2) следует сравнением производных A(L) и 2e^(L/2)/(1+L)^4: отношение стремится к единице; обе функции стремятся к бесконечности, а вторая возрастает при больших L.

Таким образом, выполненный вывод даёт только

\[
z^*B_m^{(1)}z\le\bigl(2+6HA(\log m)\bigr)z^*G_mz, \tag{4.3}
\]

с коэффициентом масштаба sqrt(m)/(log m)^4, а НЕ одну C. Этот конкретный коэффициент расходится и на любой неограниченной подпоследовательности. При этом из растущей правой части НЕ следует, что истинная форма растёт: это была бы ошибка направления.

Можно вставить другой фиксированный логарифмический показатель или более сильную классическую экспоненциальную ошибку PNT. Само по себе взятие модуля по той же схеме не поставляет требуемую совместную постоянную: потеря знака остаётся. Здесь не доказывается универсальная невозможность всех применений PNT, комплексного анализа или решета.

**Незакрытая строка — (R).** В этой работе не получено равномерного одностороннего контроля полного signed pairing. Приписать ему такой знак из (4.1) означало бы заменить расходящийся коэффициент константой без доказательства.

## 5. Что считается и что не считается результатом этой попытки

[ABSTRACT / COFINAL_FAMILY | PAPER для логической классификации; CONDITIONAL для открытого supplier.]

| Утверждение | Статус | Scope / verifier |
|---|---|---|
| (T) => RH и обратная импликация | Унаследовано из R1 | COFINAL_FAMILY / PAPER |
| Точная вся-сумма формула (3.3), края и (3.4) | Уже установлено в R1; воспроизведено | FINITE_CELL / PAPER |
| (4.1)–(4.3) | Прямой вывод из известных оценок, не новый sign supplier | COFINAL_FAMILY / PAPER |
| (R), следовательно (T) | Не доказано | COFINAL_FAMILY / CONDITIONAL |
| Невозможность какого-либо доказательства (T) | Не утверждается | — |
| RH | Не доказана | — |

Нельзя представить эту попытку как PROOF_PROGRESS: ни один открытый квантор основной оценки не закрыт. Отдельный no-go вместо (T) не предлагается. Предыдущие результаты о собственных степенях и соседних диапазонах остаются со своей прежней областью; они не превращаются в supplier для (R).

## 6. Две репрезентации, без двух новых задач

[ABSTRACT | CONDITIONAL: описание одного открытого фронта.]

1. **Полная prime-only форма на K_m.** Цель (T). Сохраняет точные атомы и все смешанные направления. Любое истинное единое верхнее ограничение непосредственно завершает consumer. Цена проверки конкретного тождества низкая; цена получения неизвестного равномерного знака не установлена.
2. **Полный центрированный интеграл.** Та же цель в (R). Непрерывная полюсная масса уже вычислена совместно; ни один остаток не имеет автоматически благоприятного знака. Отслеживание краёв стоит мало; универсальная верхняя оценка остаётся тем же неоплаченным входом.

DISCRIMINATOR здесь аналитический: действительное доказательство одной C с кванторами (T)/(R). Отсутствие найденного отрицательного вектора и оценка отдельных мод этим не являются. Численные эксперименты не предлагаются и не выполняются.

## 7. Dependency epistemics и закрытие итерации

```yaml
DOWNSTREAM_CONSUMER: PRIME_POWER_RANK_ONE_THEOREM_2
ACTUAL_CONSUMER_REQUIREMENT: ONE_CONSTANT_UPPER_BOUND_ON_ALL_CONSTRAINED_VECTORS_ALONG_ONE_UNBOUNDED_INTEGER_FAMILY
ORIGINAL_REQUESTED_OBJECT: FULL_RH_CLOSING_ARITHMETIC_BOUND
ORIGINAL_OBJECT_IS: PROVED_NECESSARY_WITHIN_THE_INHERITED_EQUIVALENCE
KNOWN_WEAKER_INTERFACES: NONE_NEW_IN_THIS_ITERATION
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: NONE_CLAIMED
REOPEN_TRIGGER: A_SOURCE_DERIVED_UNIFORM_ONE_SIDED_ESTIMATE_FOR_THE_FULL_SIGNED_PAIRING
```

Что стало меньше: в этой попытке основная математическая трудность не уменьшилась. Что убито: ничего нового. Что нельзя делать: выдавать вспомогательную теорему, точное тождество, расходящийся upper-envelope или очередную эквивалентность за доказательство (T).

Новых исполняемых тестов и новых численных predictions нет; прежним аналитическим результатам не приписывается новый outcome. Проверка документа и Git-хешей относится к доставке, а не к математическому эксперименту.

```yaml
iteration:
  target: PRIME_ONLY_UPPER_BOUND_ON_POLE_NULL_AND_MEAN_ZERO_SUBSPACE
  status: NO_PROGRESS
  attempted_strategy: DIRECT_FULL_STIELTJES_RETURN_WITH_CLASSICAL_PNT_BUDGET
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: NONE_SAME_CORE_RETAINED
  invariant_learned: ALL_VECTORS_AND_ONE_CONSTANT_ARE_THE_UNPAID_QUANTIFIERS
  forbidden_future_move: REPORT_ANOTHER_REFORMULATION_AS_THE_MISSING_SIGN
  next_decisive_step: PROVE_THE_FULL_SIGNED_UPPER_BOUND_WITH_ONE_WINDOW_INDEPENDENT_CONSTANT
```

## 8. Доставка

В репозиторий записывается только этот новый Markdown в `proshka_inbox_2026-10-31`; старые вердикты и route-state не изменяются. Ни Lean source, ни формальные axioms не добавлены. Lean/Arb gates и axiom profile: NOT_APPLICABLE. Commit и readback blob сообщаются после фактической удалённой записи. Успешная доставка не меняет математический статус NO_PROGRESS / RH_NOT_PROVED.
