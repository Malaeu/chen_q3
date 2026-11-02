# STATUS: TRY_CCM_PHASE_SPACE_CONFINEMENT_V
```yaml
OPERATIVE_CLASS: TRY_CCM_PHASE_SPACE_CONFINEMENT_V
DATE: 2026-11-02
AUTHORITY: DIRECT_OWNER_SELECT_V_AND_EXECUTE_NEXT_STEP
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_NOESCAPE_PIN: 167dff63a632f170fed2d01d88af61268ad0af7f
SOURCE_NOESCAPE_GIT_BLOB: 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc
SOURCE_RADICAL_PIN: 70f994087d479a1c4c1fd19940ebfb42ec5f0542
SOURCE_RADICAL_GIT_BLOB: 9b295e1b4ae2d0c5dab438c8514fd9329a65c34a
CARRIER: LITERAL_CCM_REAL_EVEN_N_EQUALS_M_L_EQUALS_LOG_M
RESULT: FUNCTIONAL_SELECTED_WITH_COMPACTNESS_PROOF_AND_FINITE_SOURCE_TEST
V_KIND: LOGARITHMIC_PHASE_SPACE_CONFINEMENT_COST
V_IS_PROVED_CCM_LYAPUNOV_FUNCTION: false
COFINAL_V_BOUND_PROVED: false
V_BOUND_IMPLIES_NOESCAPE: PROVED_PAPER_USING_PINNED_NOESCAPE_SUPPLIERS
RH_IMPLIES_V_BOUND: NOT_PROVED_OR_USED
ENTIRE_GROWING_ORTHONORMAL_CLUSTER_UNIFORM_V_BOUND: IMPOSSIBLE
SOURCE_DISCRETE_DRIFT_BALANCE: EXACT
RAW_DILATION_MONOTONICITY: ABSTRACT_THEOREM_SHAPE_REFUTED
FINITE_BOTTOM_V_24_TO_32: POSITIVE_INCREMENT_FLOATING_DIAGNOSTIC
FINITE_MONOTONICITY_COUNTEREXAMPLE_CERTIFIED: false
DYADIC_SUMMABLE_UPPER_DRIFT: NEXT_TARGET_NOT_PROVED
NUMERICAL_CELLS: [8, 16, 24, 32]
LITERAL_FINITE_REPLAY: COMPLETED_TWO_PRECISION_QUADRATURE_SETTINGS
EXACT_LOCAL_CONTROL_GROUPS: 6
VERIFIER: PAPER
NUMERICAL_STATUS: FLOATING_DIAGNOSTIC_NOT_CERTIFICATE
PROGRESS_CLASS: REPRESENTATION_PROGRESS
SOURCE_COFINAL_SIGN_PROGRESS: NONE_CLAIMED
INDEPENDENT_ANALYTIC_REVIEW_EXECUTED: false
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
RH_PROVED: false
ROUTE_PROMOTION: false
```

## 0. Решение

Выбираем один рабочий функционал: положительная архимедова энергия плюс логарифмическая цена пространственного ухода. Он определён на самих физических векторах, не на произвольном радикальном подъёме. Его ограниченность действительно исключает и уход массы, и уход в высокие частоты. Но закон ограниченности на точных CCM-bottoms ещё не доказан; функционал пока НЕ называется установленной энтропией Ляпунова.

Выполненный шаг: доказан количественный критерий компактности; определена величина при кратном bottom; выведен полный source-баланс её конечных приращений; выполнены literal probes и replay на m=8,16,24,32. На просмотренных точках V около 3.84, но от m=24 к m=32 возрастает. Это предупреждение против декларации простой монотонности, не интервально доказанный контрпример и не опровержение eventual/dyadic свойства.

Результат не закрывает новый кофинальный арифметический знак. Имя V и таблица не заменяют следующую оценку.

## 1. Источники и отличие от энтропии другого потока

Прочитаны через GitHub:

- S1: `docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`, на 167dff63a632f170fed2d01d88af61268ad0af7f: L15–L18, а также фиксированные residual/negative-witness suppliers. L18 уже содержит компактное phase-space наблюдаемое; ниже не заявляется его открытие заново.
- S2: `docs/routeB_bus/proshka/PROSHKA_VERDICT_RADICAL_CONCENTRATION_2026-11-02.md`, на 70f994087d479a1c4c1fd19940ebfb42ec5f0542, §§7–10. Неограниченный радикальный L2-класс не имеет максимизаторов концентрации, а его finite-carrier image есть весь carrier. Это исключает выбор V только по существованию хорошего радикального подъёма.
- S3: `docs/routeB_bus/proshka/PROSHKA_VERDICT_ENTROPY_2026-10-30.md`, на pin S1, §0 и определения: вспомогательная jump-энтропия существует, но её время не есть номер окна; sharp LSI с коэффициентом 1/4 имеет source-контрпример. Это не запрет всех иных LSI или энтропий.
- S4: `docs/routeB_bus/lowcluster_2026-11-02/core.py`, на pin S1, blob 3af915b9a3b546effefd8895ec328d8d1993aae0: исходные чётные координаты, N=m, полная von-Mangoldt сумма и формат диагностик.
- S5: локальный ранее опубликованный `PROSHKA_HADAMARD_CHECKS_2026-11-02.py`, формула W02-WR-Prime; определения сверены с S1/S4. Новая реализация ниже вычисляет соответствующие чётные элементы непосредственно.
- E1: G. Perelman, *The entropy formula for the Ricci flow and its geometric applications*, arXiv:math/0211159, Introduction and §1.2. Используется только различие «функционал плюс доказанный закон эволюции», не перенос Ricci-flow теорем на CCM. https://arxiv.org/abs/math/0211159

Источник E1 — внешняя аналогия. Все CCM-определения ниже взяты из S1/S4. Новые quasi-RH импорты не используются.

## 2. Фиксируем V без изменения метрики с m

**[ABSTRACT | PAPER; определение.]** Для вещественного чётного единичного f с нулевым продолжением положим
\[
\mathcal A[f]=\int_0^\infty j(s)\|f-T_sf\|_2^2ds,
\qquad j(s)=\frac{e^{-s/2}}{1-e^{-2s}},
\]
\[
\boxed{V[f]=\mathcal A[f]+\mathcal M_x[f],\qquad
\mathcal M_x[f]=\int_{\mathbb R}\log(1+x^2)|f(x)|^2dx.}
\tag{2.1}
\]
В Fourier-конвенции NOESCAPE:
\[
p_f(t)=|\widehat f(t)|^2/(2\pi),\quad
\mathcal A[f]=\int a(t)p_f(t)dt,
\quad a(t)=2\int_0^\infty j(s)(1-\cos ts)ds.
\]
Простая исходниковая оценка:
\[
\boxed{\tfrac12\log(1+4t^2)\le a(t)
\le\tfrac12\log(1+4t^2)+4.}
\tag{2.2}
\]
Она следует из 1/(2s)<=1/(1-e^{-2s})<=1+1/(2s) и интеграла
int_0^infinity e^{-s/2}(1-cos(ts))ds/s=(1/2)log(1+4t²).

Шкала x фиксирована в логарифмической физической координате. Не заменять x на x/L, t на tL/m и не делить V на растущую функцию m: такая нормировка может скрыть именно проверяемое бегство.

Для буквального A_m зададим не зависящий от выбора базиса скаляр
\[
\boxed{V_m=\min\{V[f]: f\in\ker(A_m-\lambda_{m,0}),\ \|f\|_2=1\}.}
\tag{2.3}
\]
Минимум в конечномерном bottom-eigenspace достигается. При простом уровне это обычное V[f_m], независимо от знака f_m. Это выбор среди точных bottoms, не выбор в произвольной near-zero полосе и не изменение A_m.

Логарифмическая частотная энергия конечна и для нулевого продолжения тригонометрического полинома с ненулевыми краевыми значениями. Глобальная H1-гладкость не предполагается.

## 3. Что bounded V даёт строго

### Лемма 1. Обе стороны escape оплачиваются одним C

**[ABSTRACT | PAPER.]** Для единичного f с V[f]<=C:
\[
\int_{|x|>R}|f|^2\le\frac C{\log(1+R^2)},\qquad
\int_{|t|>T}p_f(t)dt\le\frac C{\frac12\log(1+4T^2)}.
\tag{3.1}
\]
Это непосредственное применение неотрицательности двух слагаемых (2.1) и (2.2).

Если выбрать фиксированные R,T так, чтобы оба знаменателя были >=16C (при C=0 можно увеличить C до 1), то
\[
\boxed{\|\mathbf1_{[-R,R]}P_T^{freq}f\|_2\ge\frac12.}
\tag{3.2}
\]
Действительно, расстояние от f до этого вектора не превосходит суммы пространственного и частотного хвостов по L2, то есть 1/4+1/4.

Оператор C_(R,T)=1_[-R,R] P_T^{freq} компактен, его Hilbert–Schmidt норма в точности равна sqrt(2RT/pi). Его ядро 1_[-R,R](x)sin(T(x-y))/(pi(x-y)). Это тот же объект S1, L18.

### Лемма 2. Субуровни V компактны в L2

**[ABSTRACT | PAPER.]** В силу (3.1) пространственные хвосты равномерно малы. Для сдвига на h частоты |t|<=T дают цену h²T²||f||², остальные — не больше четырёх частотных хвостов. Сначала выбирается T, затем h. Критерий компактности L2 даёт относительную компактность субуровней. Нормировка сохраняется в сильном пределе.

### Следствие 3. Достаточный интерфейс к RH

**[COFINAL_FAMILY | PAPER, на закреплённых suppliers S1.]** Если V_m<=C на неограниченном множестве исходных m, то выбранные точные bottoms имеют ненулевой слабый, даже единичный сильный, подпоследовательный предел. По NOESCAPE L16 это даёт фиксированный theta-jet с ненулевым перекрытием, а L6 даёт RH.

Прямая проверка последней части: выбрать фиксированную конечную комбинацию r производных h с <r,f_limit>!=0. Для r_m=P_mr имеем r_m->r и ||A_mr_m||->0. Из
\[
|\lambda_{m,0}|\,|\langle r_m,f_m\rangle|
=|\langle A_mr_m,f_m\rangle|\le\|A_mr_m\|
\]
следует lambda_(m,0)->0 на подпоследовательности. Отрицательный компактный свидетель при not-RH в S1 запрещает это на любой неограниченной исходной семье.

Это достаточная импликация. RH => bounded V выбранных bottoms здесь не доказано. Bounded V сильнее минимального nonzero-weak-limit условия; оно не объявляется единственной дорогой.

### Лемма 4. Нельзя требовать bounded V на всём растущем кластере

**[ABSTRACT | PAPER.]** Если f_1,...,f_r ортонормированы и V[f_j]<=C для каждого j, то с R,T из (3.2)
\[
\frac r4\le\sum_{j=1}^r\|C_{R,T}f_j\|^2
\le\|C_{R,T}\|_{HS}^2=\frac{2RT}{\pi}.
\]
Следовательно r<=8RT/pi. Таким образом, одна константа C не может покрывать все ортонормированные уровни кластера, число которых уходит в бесконечность. Цель (2.3) относится к bottom, а не ко всему растущему near-zero спектру.

Это согласуется с S1, L3, и предотвращает чрезмерное усиление следующего задания.

## 4. Два обязательных отрицательных контроля

**[ABSTRACT | PAPER; не eigenfunctions CCM.]** Для фиксированной чётной Schwartz-функции:

1. Симметричная пара далеко раздвинутых нормированных пакетов имеет V->infinity за счёт log(1+x²). Можно брать именно h(x-a)+h(x+a): это буквальная радикальная семья S2, но обычная пространственная концентрация уходит.
2. Нормированный phi(x)cos(Tx) имеет ограниченную пространственную часть, но A->infinity порядка log T. Поэтому малая пространственная ширина не скрывает частотное escape.

Положительный функционал выбран не потому, что он называется энтропией, а потому, что эти два испытания имеют правильный исход.

### Свободная дилатация не даёт знака

**[ABSTRACT | PAPER.]** Для U_tau f=e^(-tau/2)f(e^-tau x), в области V:
\[
\boxed{\left.\frac d{d\tau}V[U_\tau f]\right|_0
=\int\frac{2x^2}{1+x^2}|f(x)|^2dx
-\|f\|_2^2-\int_0^\infty (sj(s))'Q_f(s)ds.}
\tag{4.1}
\]
Архимедова производная получена заменой переменной в kernel, без f'. Функция (sj)' принадлежит L1, её интеграл равен -1/2. Пространственная производная ограничена числом 2||f||².

Для f_sigma(x)=(sqrt(pi)sigma)^(-1/2)exp(-x²/(2sigma²)) имеем Q=2exp(-s²/(4sigma²)). Тогда (4.1) стремится к -1 при sigma->0 и к +2 при sigma->infinity, по dominated convergence. Значит общий закон V[U_tau f] не имеет одного знака. Это строгий контроль универсального вывода о дилатации, не контрпример к возможному закону точных CCM-bottoms.

## 5. Точная эволюция включает движение самого дна

**[FINITE_CELL | PAPER; простой уровень, фиксированный N.]** Пусть K_N(L) — исходная непрерывная матрица, B_N(L) — матрица функционала V на том же ортонормированно перенесённом носителе, c_i — её нормированные K-eigenvectors. Точка над матрицей означает L d/dL. Тогда
\[
\boxed{\frac d{d\log L}V[f_{N,0,L}]
=c_0^T\dot B_Nc_0
-2\sum_{i\ge1}\frac{(c_i^TB_Nc_0)(c_i^T\dot K_Nc_0)}{\lambda_i-\lambda_0}.}
\tag{5.1}
\]
Первое слагаемое — (4.1). Второе — изменение минимизирующего вектора. Доказательство: в gauge c_0^T c'_0=0 дифференцировать Kc_0=lambda_0 c_0, спроецировать на c_i, затем дифференцировать c_0^TBc_0. Каждый знаменатель положителен, но числитель не обязан быть неотрицательным.

В (5.1) нельзя удалить кластерные члены или заменить их универсальной gap-оценкой, которой нет. При кратном bottom (5.1) не заявляется: используются конечные вариационные сравнения с (2.3). При переходе N=m -> m+1 дополнительно меняется carrier. Межоконная монотонность энергии не доказывает монотонность V; точный 2x2-контроль приведён в коде.

Поэтому основная следующая цель сформулирована дискретно, без предположения простоты и без перехода N=infinity.

## 6. Выполненный literal-source тест

**[FINITE_CELL | PAPER for formulas; FLOATING_DIAGNOSTIC for computed values.]** Использован буквальный N=m, L=log m, все von-Mangoldt атомы n<=m, полный полюс и WR-формула. Новые high-mode направления в eigenproblem не добавлялись. Частотная энергия считается архимедовой матрицей, без усечения интеграла по t.

| m | lambda_0 (диагностика) | M_x bottom | A bottom | V bottom | V верхнего уровня |
|---:|---:|---:|---:|---:|---:|
| 8 | 1.0239258710e-19 | 0.024896756593 | 3.854748223546 | 3.879644980139 | 7.190186350685 |
| 16 | 5.4561380117e-38 | 0.026362612102 | 3.817023825528 | 3.843386437630 | 7.526424910054 |
| 24 | 2.6905128126e-54 | 0.026487095800 | 3.813752930637 | 3.840240026438 | 8.054742487383 |
| 32 | 8.1805955424e-70 | 0.026383832618 | 3.816184244632 | 3.842568077250 | 7.933155813218 |

Первичные настройки: 80/90/100 десятичных знаков по клеткам, GL64 в каждой из 8 панелей. Replay: 120 знаков для m<=24, 140 для m32, GL96 в каждой панели. Все 32-значные опубликованные V/M_x/A/prime/pole поля совпали для трёх выбранных уровней каждой клетки. Это НЕ независимый аналитический аудит: один автор и одна реализация, увеличены точность и порядок квадратуры. Ошибки квадратуры и eigenpair не ограждены интервалами.

Общий replay достиг лимита инструмента после сохранённых m8,m16; m24 отдельно выполнен до конца. m32 также выполнен и replay-нут отдельно. Незавершённый запуск не выдан за завершённый.

Особенно важное наблюдение:
\[
V_{32}-V_{24}\approx+0.00232805081218.
\tag{6.1}
\]
Таким образом, данные НЕ поддерживают фразу «V уже монотонна на всех m». Это конечный floating warning; eventual monotonicity или существование summable upper drift этим не опровергнуты. На заранее стандартных dyadic парах 8->16 и 16->32 приращения отрицательны, но две пары не являются законом.

Для 24->32:
\[
\Delta M_x\approx-0.000103263182975,\quad
\Delta\mathcal P\approx-0.001055912681110,\quad
\Delta\mathcal O\approx-0.003487226676269,
\]
где P — prime-корреляция, O — положительный pole-square. Уменьшение pole-square в точном балансе увеличивает V сильнее двух остальных убываний. Это диагностика механизма, не закон его масштаба.

Контроль формы (4.1) и 2x2-примеры заданы до исполнения их тестов; 6 групп прошли. Таблица — exploratory: заранее заявленного численного прогноза о её монотонности не было. Не производится ретроактивная регистрация такого прогноза.

## 7. Один следующий математический шаг, с настоящим источником

**[FINITE_CELL | PAPER; точное тождество.]** Для выбранного bottom f_m положим
\[
\mathcal P_m=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}Q_{f_m}(\log n),\quad
\mathcal O_m=|\langle\sqrt2\cosh(x/2),f_m\rangle|^2,\quad
\mathcal M_m=\mathcal M_x[f_m].
\]
Полная собственная энергия даёт
\[
\boxed{V_m=\lambda_{m,0}+c_*+\mathcal P_m-\mathcal O_m+\mathcal M_m.}
\tag{7.1}
\]
Следовательно, для заранее фиксированного dyadic расписания m_k=2^k:
\[
\boxed{V_{2m}-V_m=
(\lambda_{2m,0}-\lambda_{m,0})
+(\mathcal P_{2m}-\mathcal P_m)
-(\mathcal O_{2m}-\mathcal O_m)
+(\mathcal M_{2m}-\mathcal M_m).}
\tag{7.2}
\]
В prime-разности точно остаются и старые атомы с изменённым профилем, и новые:
\[
\mathcal P_{2m}-\mathcal P_m=
\sum_{n\le m}\omega_n[Q_{f_{2m}}(a_n)-Q_{f_m}(a_n)]
+\sum_{m<n\le2m}\omega_nQ_{f_{2m}}(a_n).
\tag{7.3}
\]
Никакая часть не оценивается здесь посредством неоплаченной независимости простых; нулевой endpoint-correlation соблюдён. (7.2) не есть искомая оценка.

**[COFINAL_FAMILY | CONDITIONAL; следующий supplier, НЕ доказан.]** Ищем вывод непосредственно из источника:
\[
\boxed{V_{2^{k+1}}-V_{2^k}\le\varepsilon_k,
\qquad \varepsilon_k\ge0,\quad \sum_{k\ge k_0}\varepsilon_k<\infty.}
\tag{T}
\]
Последовательность epsilon должна иметь независимый аналитический budget, а не определяться как положительная часть неизвестного приращения. Достаточный пример формы бюджета — C/(k+1)^2 с одной source-константой, но именно этот показатель не объявляется обязательным или ожидаемым.

Телескопирование (T) даёт bounded V на неограниченной исходной семье. По §3 это доказывает RH через поставщиков NOESCAPE. Не нужно заранее доказывать V_{m+1}<=V_m при каждом m или идентифицировать все eigenfunctions с конкретной лестницей.

(T) сильнее простой boundedness: ограниченная осциллирующая последовательность может иметь несуммируемые положительные приращения. Поэтому неудача доказать (T) не убивает прямой target sup_j V_(m_j)<infinity. И ни один из них не объявляется необходимым следствием RH.

### Единственная CODEX DIRECTIVE

**CCM_PHASE_SPACE_V_DYADIC_SOURCE_DRIFT**

На неизменном source N=m,L=log m независимо проверить V-реализацию и баланс (7.1)–(7.3), затем выполнить одну аналитическую попытку оценить полное подписанное приращение (7.2) сверху суммируемым, заранее определённым бюджетом. Раздельные растущие абсолютные оценки prime/pole/движения профиля не засчитывать как компенсацию. Сохранить min-V выбор в кратном bottom; не выбирать произвольную точку near-zero кластера. Любой перенос вектора между carrier-ами должен иметь явный Gram/projection-return бюджет.

Успех: действительный (T) или более слабый uniform V-bound на заданной неограниченной семье. Только тогда consumer закрыт. Неуспех: один точный неподконтрольный подписанный член с указанием, какую зависимость источника потерял применённый bound. Простое повторение (7.2) не есть progress.

Вычислительный gate: выполнить код Appendix с --m 8 16 24 32 и двумя указанными настройками; вернуть значения, исходные нормировки и все неоплаченные ошибки. Это gate реализации, не доказательство (T). Новый большой eigenvalue scan без изменяющего диагноз вопроса не требуется.

## 8. Два представления и epistemic closeout

| Представление | Применение / сила / цена |
|---|---|
| Выбранное V: confining position + literal arch energy | Проверяемый компактный sublevel и точный source drift; высокая сила против двух видов escape / невысокая finite цена, высокая аналитическая |
| Фиксированное компактное C_(R,T), -log(||C f||²) | Минимальный NOESCAPE-свидетель из S1 L18; меньшее требование, но без source-law остаётся старой эквивалентностью / низкая finite цена, неизвестная аналитическая |

Три стыка проверены: compactness/Slepian даёт критерий §3; entropy/Perelman не переносит монотонность другого потока; spectral perturbation даёт §5 с неоплаченным source sign. Vanishing identity theta-радикала не зануляет (7.2) на настоящих bottoms. Collapse-object — независимо ограниченный подписанный dyadic drift, не имя V.

DOWNSTREAM_CONSUMER: nonzero weak subsequential bottom limit => pinned NOESCAPE => RH.
ACTUAL_CONSUMER_REQUIREMENT: one persistent compact-observable mass, not full-cluster convergence.
ORIGINAL_REQUESTED_OBJECT: choose an entropy-like V and make a next step.
ORIGINAL_OBJECT_IS: NOT_PROVED_NECESSARY; selected V is a sufficient stronger interface.
FAILURE_TYPE: NO_DERIVATION of source drift bound.
EPISTEMIC_STATUS: RESEARCH_DEBT, not route impossibility.
REOPEN_TRIGGER: actual signed comparison in (7.2), or weaker compact-observable upper-loss bound.
DISCRIMINATOR: translated radical packets and modulated packets must be detected; exact bottom motion and mode insertions must not be omitted.
NOVELTY_AXIS: fixed physical compactness metric and executed source test, not a claimed new entropy theorem.

Не убит ни RH-маршрут, ни V-кандидат. Отсечён общий inference «чистая дилатация / минимальность / меньшая энергия сами делают V монотонной». Полная boundedness и почти-монотонность на исходном источнике не доказаны. Научный статус этого шага — выбор и проверка представления, не закрытый кофинальный знак.

## Appendix A. Reproducible code

Код ниже совпадает с отдельным скачиваемым Python-файлом. m в --m заменяется только нужными исходными целыми, например --m 8 16 24 32; --output задаёт путь JSON. Все проверки выполняются в текущем процессе, без фоновых заданий. Никакого Lean/Arb gate здесь нет.

```python
#!/usr/bin/env python3
"""Exact controls and a literal finite-CCM diagnostic for a proposed V.

  uv run --with sympy --with mpmath PROSHKA_PHASE_SPACE_V_CHECKS_2026-11-02.py
  uv run --with sympy --with mpmath PROSHKA_PHASE_SPACE_V_CHECKS_2026-11-02.py --diagnostic --m 8 16 24 --dps 90 --order 64 --output phase_space_v.json

--m: original cells, always N=m and L=log(m). --order: GL nodes per panel;
there are eight panels. --output: diagnostic JSON destination, e.g. v.json.
Numerical values have no interval/quadrature/tail certificate. The frequency
energy is evaluated through the exact archimedean form, not a truncated
Fourier integral. All prime powers through m are included.
"""
from __future__ import annotations
import argparse
import json
import time
from pathlib import Path


def exact_checks() -> None:
    import sympy as s
    x,tau=s.symbols('x tau', real=True)
    assert s.simplify(s.diff(s.log(1+s.exp(2*tau)*x*x),tau).subs(tau,0)-2*x*x/(1+x*x))==0
    print('PASS 1 position dilation multiplier')
    z=s.symbols('z',positive=True)
    j=s.exp(-z/2)/(1-s.exp(-2*z))
    mj=s.diff(z*j,z)
    assert s.limit(z*j,z,0,dir='+')==s.Rational(1,2)
    assert s.limit(z*j,z,s.oo)==0
    assert s.limit(mj,z,0,dir='+')==s.Rational(1,4)
    print('PASS 2 archimedean endpoints: integral m_j = -1/2')
    th=s.symbols('th', real=True)
    c=s.Matrix([s.cos(th),s.sin(th)])
    d=s.Matrix([-s.sin(th),s.cos(th)])
    A=d*d.T
    B=s.diag(0,1)
    Apr=s.diff(A,th)
    V=(c.T*B*c)[0]
    rhs=-2*(c.T*B*d)[0]*(d.T*Apr*c)[0]
    assert s.trigsimp(s.diff(V,th)-rhs)==0
    assert s.trigsimp(s.diff(V,th)-s.sin(2*th))==0
    print('PASS 3 exact spectral response; both signs despite exact ground state')
    for bj in [s.Rational(1,2),s.Integer(2)]:
        An=s.diag(0,-1); Bn=s.diag(1,bj)
        new=s.Matrix([0,1]); old=s.Matrix([1,0])
        assert (new.T*An*new)[0] < (old.T*An*old)[0]
        assert (new.T*Bn*new)[0]-(old.T*Bn*old)[0]==bj-1
    print('PASS 4 mode insertion lowers energy but need not lower V')
    C=s.symbols('C',nonnegative=True)
    a0,prime,pole,position,lam,cstar=s.symbols('a0 prime pole position lam cstar',real=True)
    assert s.expand((lam+cstar+prime-pole+position).subs(lam,a0-cstar-prime+pole)-(a0+position))==0
    print('PASS 5 full signed source balance keeps the pole and all mixed signs')
    assert 1-s.Rational(1,4)-s.Rational(1,4)==s.Rational(1,2)
    print('PASS 6 simultaneous time/frequency tail thresholds')
    print('ALL 6 EXACT CONTROL GROUPS PASSED')


def mangoldt(n: int, mp):
    for p in range(2,n+1):
        if n%p==0:
            q=n
            while q%p==0:q//=p
            return mp.log(p) if q==1 else mp.mpf(0)
    return mp.mpf(0)


def cell(m: int, dps: int, order: int) -> dict:
    import mpmath as mp
    mp.mp.dps=dps
    L=mp.log(m); N=m
    pi=mp.pi; sq2=mp.sqrt(2)
    gn,gw=mp.gauss_quadrature(order,'legendre')
    nodes=[]
    for panel in range(8):
        lo=mp.mpf(panel)/8; hi=mp.mpf(panel+1)/8
        for z,w in zip(gn,gw):
            nodes.append(((lo+hi)/2+(hi-lo)*z/2,w*(hi-lo)/2))
    ss=[L*y for y,w in nodes]
    ww=[L*w for y,w in nodes]
    sins=[[mp.sin(2*pi*n*y) for y,w in nodes] for n in range(N+1)]
    coss=[[mp.cos(2*pi*n*y) for y,w in nodes] for n in range(2*N+1)]
    xpos=[mp.log1p((L*(y-mp.mpf('.5')))**2) for y,w in nodes]
    xpos_mom=[mp.fsum(w*x*c for (y,w),x,c in zip(nodes,xpos,coss[n])) for n in range(2*N+1)]
    js=[mp.exp(-s/2)/(-mp.expm1(-2*s)) for s in ss]
    sinmom=[mp.fsum(w*j*sn for w,j,sn in zip(ww,js,sins[n])) for n in range(N+1)]
    diag=[]
    for n in range(N+1):
        # Stable raw WR diagonal, including the source subtraction at s=0.
        vals=[]
        for (y,w),s in zip(nodes,ss):
            e=mp.exp(s/2)
            num=mp.expm1(s/2)-e*y-2*e*(1-y)*mp.sin(pi*n*y)**2
            vals.append(L*w*num/mp.sinh(s))
        diag.append(mp.fsum(vals))
    cstar=mp.euler+mp.log(8*pi)+pi/2
    wrconst=mp.euler+mp.log(4*pi*mp.tanh(L/2))
    ds=[mp.mpf(1)]+[sq2]*N
    arch=mp.zeros(N+1); prime=mp.zeros(N+1); pos=mp.zeros(N+1)
    atoms=[(n,mp.log(n)/L,mangoldt(n,mp)/mp.sqrt(n)) for n in range(2,m+1) if mangoldt(n,mp)]
    for i in range(N+1):
        for k in range(i,N+1):
            if i==k:
                av=cstar-wrconst-diag[i]+(sinmom[i]/(pi*i) if i else 0)
            else:
                av=ds[i]*ds[k]/pi*(i*sinmom[i]-k*sinmom[k])/(i*i-k*k)
            def q(r):
                if i==k:
                    return 2*(1-r)*mp.cos(2*pi*i*r)-(mp.sin(2*pi*i*r)/(pi*i) if i else 0)
                return ds[i]*ds[k]/pi*(k*mp.sin(2*pi*k*r)-i*mp.sin(2*pi*i*r))/(i*i-k*k)
            pv=mp.fsum(w*q(r) for n,r,w in atoms)
            xv=ds[i]*ds[k]*(xpos_mom[abs(i-k)]+xpos_mom[i+k])/2
            arch[i,k]=arch[k,i]=av
            prime[i,k]=prime[k,i]=pv
            pos[i,k]=pos[k,i]=xv
    pole=mp.matrix([4*sq2*ds[n]*L**mp.mpf('1.5')*mp.sinh(L/4)/(L*L+16*pi*pi*n*n) for n in range(N+1)])
    A=arch-cstar*mp.eye(N+1)-prime+pole*pole.T
    ev,U=mp.eigsy(A)
    B=arch+pos
    rows=[]
    for i in (0, min(1,N),N):
        c=U[:,i]
        ar=(c.T*arch*c)[0]; xp=(c.T*pos*c)[0]
        pp=(c.T*prime*c)[0]; pol=(c.T*pole)[0]**2
        val=ar+xp
        source=ev[i]+cstar+pp-pol+xp
        rows.append(dict(index=i,lambda_=mp.nstr(ev[i],32),V=mp.nstr(val,32),position=mp.nstr(xp,32),arch=mp.nstr(ar,32),prime=mp.nstr(pp,32),pole=mp.nstr(pol,32),source_balance_error=mp.nstr(abs(source-val),8),coefficients=[mp.nstr(z,40) for z in c]))
    return dict(m=m,N=N,L=mp.nstr(L,40),dps=dps,GL_order_per_panel=order,panels=8,
                status='FLOATING_DIAGNOSTIC_NOT_CERTIFICATE',eigen_residual=mp.nstr(mp.norm(A*U-U*mp.diag(ev)),8),levels=rows)


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--diagnostic',action='store_true')
    p.add_argument('--m',nargs='+',type=int,default=[8,16,24])
    p.add_argument('--dps',type=int,default=90)
    p.add_argument('--order',type=int,default=64)
    p.add_argument('--output',type=Path,default=Path('phase_space_v.json'))
    a=p.parse_args()
    exact_checks()
    if not a.diagnostic:return
    if min(a.m)<2 or a.dps<30 or a.order<16:
        p.error('Require m>=2, dps>=30, order>=16.')
    out=[]; start=time.monotonic()
    for i,m in enumerate(a.m,1):
        out.append(cell(m,a.dps,a.order))
        elapsed=time.monotonic()-start
        eta=elapsed*(len(a.m)-i)/i
        n=20*i//len(a.m)
        print('['+'#'*n+'-'*(20-n)+f'] {i}/{len(a.m)} ETA {eta:.1f}s',flush=True)
        print(json.dumps({k:v for k,v in out[-1].items() if k!='levels'}),flush=True)
        for v in out[-1]['levels']:print(json.dumps({k:z for k,z in v.items() if k!='coefficients'}),flush=True)
        a.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(f'WROTE {a.output}')

if __name__=='__main__':main()

```
