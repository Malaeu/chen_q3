# STATUS: TRY_CCM_VAUGHAN_SHORT_INVERSE_ENERGY_Q15
```yaml
OPERATIVE_CLASS: TRY_CCM_VAUGHAN_SHORT_INVERSE_ENERGY_Q15
VERDICT_CODE: ACTUAL_SHORT_INVERSE_LCM_ENERGY_PAID_OPTIMAL_SEPARATED_ROW_CERTIFICATE_RETAINS_HALF_POWER
DATE: '2026-10-24'
REQUEST_FILE: PROSHKA_CCM_VAUGHAN_JOINT_Q15_2026-10-24.txt
REQUEST_BYTES: 126176
REQUEST_LF: 2129
REQUEST_SHA256: 61fea7c4fc6a3438f9d15e46a824349828bd222d4b4c122d5e66b3f9a8b8d4e7
REQUEST_COMMIT_AS_SUPPLIED: ff81762fd264498f4f445d5dd6d21dad4568f4dd
REQUEST_READ: COMPLETE_TOP_REQUEST_AND_ALL_TWELVE_SOURCE_BODIES
MANIFEST: ALL_TWELVE_BYTE_COUNTS_AND_SHA256_MATCH
BOOTSTRAP_REPOSITORY: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_WITH_ORIGINAL_THREE_CONSTRAINT_SPARSE_BAND
SCHEDULE: N=m; L=log(m); M=R=U=V=floor(m^epsilon); fixed 0<epsilon<1/32
CHOSEN_MECHANISM: Actual short-inverse LCM energy; weighted noncommutative Cauchy; complete row-energy return and exact optimization of all positive scalar row weights
ADJUDICATION: NO_NEW_FULL_ARITHMETIC_POWER
NEW_PAPER_OUTPUTS:
  - Exact floor and harmonic LCM formulas for actual nu_U squared
  - Totient diagonalization and 1/(3 H_U) <= Q_U <= H_U^3, with H_U the harmonic number
  - Complete noncommutative weighted-square loss with all row and prime-factor mixed products
  - Exact infimum of the separated-row certificate equals twice the actual coefficient-weighted absolute row mass
  - Actual distinct-prime products force that certificate to be at least sqrt(m)/(32 log(m)) eventually
NEW_FULL_CCM_EXPONENT: NONE
COMPLETED_NEW_CERTIFICATE_POWER: ONE_HALF_UP_TO_FIXED_LOGARITHMS
BEST_INHERITED_ELEMENTARY_SOURCE_BOUND: S_m <= 12 sqrt(m) P
BEST_INHERITED_CONDITIONAL_POWER: 3/8, unchanged conditional ZF78, comparison only
RH_ZF78_MERTENS_VARIANCE_AS_NEW_PREMISE: false
ALL_WEIGHTS_HYPERBOLA_POWERS_ORIGINAL_P_AND_MIXED_TERMS: RETAINED_UNTIL_EXPLICIT_PROVED_INEQUALITIES
SCOPED_OBSTRUCTION:
  KILL_SCOPE: THEOREM_SHAPE
  SHAPE: Uniform sub-half-power budget from the displayed weighted Cauchy certificate followed by ||H_a||<=2 B_a, even after optimizing all positive scalar row weights
  EVIDENCE_KIND: Exact certificate minimization plus actual rough-semiprime lower bound using ordinary PNT
  EVIDENCE: Sections 5 and 6; not a spectral lower bound for actual II or CCM
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_FOR_THIS_PRECISE_CERTIFICATE_SHAPE
ACTUAL_SOURCE_ROUTE_KILL_SCOPE: NONE
ACTUAL_TARGET_FAILURE_TYPE: NO_DERIVATION
ACTUAL_TARGET_EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_STRUCTURAL_STRENGTHENING: Replacing a one-sided form by a square and discarding its full weighted-Cauchy defect
FIRST_UNPAID_ARITHMETIC_LINE: A smaller bound for the actual weighted projected row energy or a direct upper sign before that strengthening
PROGRESS_CLASS: FALSIFICATION_PROGRESS
CONSUMER_POWER_PROGRESS: NONE
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
REPOSITORY_WRITES: NONE
LEAN_RUNS: 0
ARB_RUNS: 0
INDEPENDENT_REVIEW: NOT_RUN
SOURCE_REPLAY: 8192 exact formal-log cases; JSON matches supplied S3
NEW_EXACT_LOCAL_CONTROLS: 7801
NEW_NONINTERVAL_DIAGNOSTIC_CASES: 3 at 50 decimal digits
FULL_CCM_SPECTRA_COMPUTED: false
CF22_PYSR: PARKED_REOPENABLE
FULL_SP_G1_G3_RH: OPEN_NOT_CLAIMED
PX_RH_CLAIM: NOT_MADE
```

Ы. **Полного арифметического выигрыша Q15 не даёт.** Испытан один конкретный способ использовать короткую обратную свёртку: сначала точно вычислить её делительную энергию, затем перенести её на полный билинейный оператор с тем же матричным весом. Все коэффициенты и смешанные члены выписаны до неравенств. После законного, но грубого завершения получена половинная степень.

**Более сильный результат этой проверки — точная граница выбранного сертификата.** После замены каждой полной матричной строки её положительной скалярной ценой никакой подбор положительных весов Коши не даёт показатель меньше `1/2`. Это доказано на настоящих коэффициентах `nu_U` и `Lambda`, а не на произвольных знаках. Однако сам этот скалярный возврат теряет исходную корреляцию. **Для настоящей II, полной CCM или возможности другого совместного доказательства запрета не установлено.**

## 0. Источник, чтение, статус и область утверждений

**[ABSTRACT | PAPER — происхождение.]** Прочитан целиком приложенный UTF-8: 126176 байт, 2129 LF. Хеш вычислен из реально смонтированных байтов. Ожидаемый общий хеш в кратком сообщении владельца отсутствовал; он не объявляется независимо подтверждённым pin. Все 12 тел S1–S12 извлечены по буквальным `BEGIN SOURCE`/`END SOURCE`; их размеры и SHA-256 совпали с предоставленным манифестом. Манифест помещён ниже.

Действующее поручение — начало Q15, а не исторические директивы внутри источников. `REQUEST_COMMIT` принят как привязка пакета; текущий HEAD, транзитивные Lean-зависимости и состояние общей очереди не проверялись. Через живой GitHub прочитан только bootstrap на `rh_clean`. Записей в репозиторий, платных внешних обращений, отправок другим агентам и новых build не было.

Приняты **в своих исходных областях**: буквальные `P,F,Q_M`, short/full-k нормы S1 и S5, непрерывное rank-two равенство S4, элементарная `W(x)<=6sqrt(x)`, архимедова плата, отдельный sparse-band witness S6–S7. Они не выдаются за заново независимо проверенную всю цепочку. Условные `3/8` из S12 — только сравнение; ZF78 нигде не является входом новых безусловных выводов.

Внешний вход для нижней границы **бюджета** — лишь обычная безусловная PNT, точнее `pi(2x)-pi(x)~x/log x`. Ни RH-размер ошибки, ни новая zero-free полоса не нужны. DLMF 27.5 сверяет нормировки свёртки и тождества с `phi`; сами конечные расчёты доказаны ниже.

Теги: **FINITE_CELL** означает утверждение для каждого фиксированного исходного конечного объекта; **COFINAL_FAMILY** — заявленные кванторы по растущему `m`; **PAPER** — письменное доказательство, не Lean/Arb. **CONDITIONAL** отмечает только реально условные входы, не обещанные результаты.

## 1. Неизменённая полная форма

**[FINITE_CELL | PAPER — определения из S1, S5–S7.]**

\[
L=\log m,\qquad \omega_j=2\pi j/L,\qquad
\Omega=2\pi M/L,
\]
\[
f(t)=\frac1{\sqrt L}\sum_{|j|\le M}c_je^{i\omega_jt}\mathbf1_{[0,L]}(t),
\qquad c\in\operatorname{ran}P.
\tag{1.1}
\]

Частоты не меняются на `2pi j/log M`. Полоса дополняется нулями в исходный carrier `N=m`. Тот же `P` обеспечивает
\[
f(0)=f(L)=0,\qquad
\int_0^Le^{t/2}f(t)\,dt=\int_0^Le^{-t/2}f(t)\,dt=0,
\qquad\|f\|_2=\|c\|_2.
\tag{1.2}
\]

Пусть
\[
A(n)=P Q_M(\log n)P,
\quad \|A(n)\|\le2,
\quad A(m)=0,
\]
\[
S_m=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}A(n).
\tag{1.3}
\]

Для комплексного `f` определим **автокорреляцию** — overlap исходной функции со своим сдвигом:
\[
r_f(s)=\int_0^{L-s}\overline{f(t)}f(t+s)\,dt.
\]
Тогда `c*A(n)c=2 Re r_f(log n)`. Никакие смешанные моды не удаляются.

Оставляем буквальные конечные коэффициенты
\[
\nu_U(a)=\sum_{\substack{d\mid a\\d>U}}\mu(d),
\qquad
b_V(v)=\sum_{\substack{k\mid v\\k>V}}\Lambda(k).
\]
Исходная большая сумма:
\[
\boxed{
\mathrm{II}_{m;U,V}
=\sum_{\substack{a>U,\ b>V\\ab\le m}}
\frac{\nu_U(a)\Lambda(b)}{\sqrt{ab}}A(ab).
}
\tag{1.4}
\]
Она равна варианту `mu(d)b_V(v)` из задания. При `a>U`,
\[
\nu_U(a)=-\sum_{\substack{d\mid a\\d\le U}}\mu(d).
\tag{1.5}
\]

**Исходный знак** для каждого допустимого `c`:
\[
c^*\mathrm{II}c
=2\Re\sum_{\substack{a>U,b>V\\ab\le m}}
\frac{\nu_U(a)\Lambda(b)}{\sqrt{ab}}r_f(\log(ab)).
\tag{1.6}
\]
Все `a,b` в этом выражении используют **одну** функцию `f`, а не независимо выбранные фазы или тесты.

Фиксируем также произвольный настоящий вес
\[
W=PWP\succeq0,\qquad\operatorname{Tr}W=1.
\tag{1.7}
\]
Нормированный вес нужен только когда `ran P` ненулево. Для общего следа все оценки однородно умножаются на `Tr W`.

В конце, как в запросе,
\[
M=R=U=V=\lfloor m^\epsilon\rfloor,
\qquad0<\epsilon<1/32\quad\text{фиксировано до }m\to\infty.
\tag{1.8}
\]

## 2. Конкретный арифметический вход: энергия короткой обратной свёртки

Это место использует **настоящую** связь (1.5), которой нет у произвольных ограниченных коэффициентов. Проверяем, достаточно ли этой связи после полного переноса; положительный ответ не предполагается.

### 2.1. Точная floor-энергия

**Лемма 1 [FINITE_CELL | PAPER].** Обозначим
\[
\sigma_U(a)=\sum_{\substack{d\mid a\\d\le U}}\mu(d),\qquad
h_n=\sum_{j=1}^n\frac1j,\quad h_0=0.
\]
Для целых `X>=U>=1`:
\[
\boxed{
\sum_{U<a\le X}\nu_U(a)^2
=
\sum_{d,e\le U}\mu(d)\mu(e)
\left\lfloor\frac{X}{[d,e]}\right\rfloor-1.
}
\tag{2.1}
\]
Здесь `[d,e]` — **наименьшее общее кратное**.

**Доказательство.** В квадрате `sigma_U(a)` раскрываются все пары `d,e`, в том числе разные. Условие `d|a,e|a` эквивалентно `[d,e]|a`. Для `1<=a<=U` полный делительный ряд Мёбиуса равен `1` при `a=1` и `0` при остальных `a`. Следовательно, исключение этого диапазона вычитает ровно единицу. Для `a>U` имеем `nu_U=-sigma_U`. Все члены конечны. ∎

В частности, при
\[
q_U=\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{[d,e]},
\]
получаем явную абсолютную ошибку:
\[
\boxed{
\left|1+\sum_{U<a\le X}\nu_U(a)^2-Xq_U\right|\le U^2.
}
\tag{2.2}
\]
Это цена целочисленных краёв; её не зануляем по знаку.

Для гармонического веса также **точно**:
\[
\boxed{
Z_U(X):=\sum_{U<a\le X}\frac{\nu_U(a)^2}{a}
=
\sum_{d,e\le U}\frac{\mu(d)\mu(e)}{[d,e]}
 h_{\lfloor X/[d,e]\rfloor}-1.
}
\tag{2.3}
\]

### 2.2. Все смешанные делители в положительной диагонализации

**Лемма 2 [FINITE_CELL | PAPER].**
\[
\boxed{
q_U=\sum_{r\le U}\varphi(r)
\left(\sum_{\substack{d\le U\\r\mid d}}\frac{\mu(d)}d\right)^2,
\qquad
\frac1{3h_U}\le q_U\le h_U^3.
}
\tag{2.4}
\]

**Доказательство.** Из `gcd(d,e)=sum_(r|d,r|e) phi(r)` и `[d,e]=de/gcd(d,e)` получается точная первая формула. Пишем `y_r=sum_(r|d,d<=U)mu(d)/d`. Делительная инверсия даёт
\[
\sum_{r\le U}\mu(r)y_r
=\sum_{d\le U}\frac{\mu(d)}d\sum_{r\mid d}\mu(r)=1.
\]
Неравенство Коши поэтому даёт
\[
1\le q_U\sum_{r\le U}\frac{\mu(r)^2}{\varphi(r)}.
\]
Далее
\[
\sum_{r\le U}\frac{\mu(r)^2}{\varphi(r)}
\le\sum_{r\le U}\frac1{\varphi(r)}
\le h_U\prod_p\left(1+\frac1{p(p-1)}\right)
\le e\,h_U<3h_U.
\]
Во втором неравенстве использовано точное `n/phi(n)=sum_(d|n)mu(d)^2/phi(d)`; последний продукт ограничен через `sum_(n>=2)1/(n(n-1))=1`. Это не гипотеза о распределении простых.

Для верхней границы разрешён грубый, явно обозначенный шаг:
\[
q_U\le\sum_{d,e\le U}\frac1{[d,e]}
=\sum_{r\le U}\frac{\varphi(r)}{r^2}h_{\lfloor U/r\rfloor}^2
\le h_U^3.
\]
∎

В частности,
\[
\boxed{
\sum_{U<a\le X}\nu_U(a)^2
\ge\frac{X}{3h_U}-U^2-1.
}
\tag{2.5}
\]
При `X>>U^2 h_U` квадрат этого фактического коэффициента не имеет произвольного степенного разрежения. **Это не нижняя оценка signed-суммы II.**

Для последующего переноса достаточна равномерная верхняя граница
\[
\boxed{Z_U(X)\le h_X h_U^3.}
\tag{2.6}
\]
Действительно, раскрываем квадрат `sum_(d|a,d<=U)|mu(d)|`, суммируем положительные члены с весом `1/a`, используем `[d,e]` и предыдущую оценку `sum 1/[d,e]<=h_U^3`.

**Итог этого этапа:** цена квадрата коэффициентов логарифмическая, без искусственного `U` или `U^2` в итоговом гармоническом верхе (2.6). Но уменьшение цены одного входа не равно уменьшению полной степени билинейной формы. Никакой приоритет для классической LCM-алгебры не заявляется.

## 3. Полная матричная билинейная сборка — до неравенства Коши

**[FINITE_CELL | PAPER].** Положим
\[
A_*:=\left\lfloor\frac m{V+1}\right\rfloor,
\]
\[
\mathsf H_a=
\sum_{\substack{b>V\\ab\le m}}
\frac{\Lambda(b)}{\sqrt b}A(ab),
\quad
\alpha_a=\frac{\nu_U(a)}{\sqrt a},
\quad
\mathsf B_a=
\sum_{\substack{b>V\\ab\le m}}\frac{\Lambda(b)}{\sqrt b}.
\tag{3.1}
\]
Тогда
\[
\boxed{\mathrm{II}=\sum_{U<a\le A_*}\alpha_a\mathsf H_a.}
\tag{3.2}
\]
При `A_*<=U` эта сумма пуста. Нулевые строки или `nu=0` можно удалить лишь как буквальные нули.

**Все** смешанные произведения полного квадрата:
\[
\begin{aligned}
\mathrm{II}^2
={}&\sum_{a,a'>U}\frac{\nu_U(a)\nu_U(a')}{\sqrt{aa'}}
\sum_{\substack{b,b'>V\\ab\le m,\ a'b'\le m}}
\frac{\Lambda(b)\Lambda(b')}{\sqrt{bb'}}\\
&\qquad\times P Q_M(\log(ab))P Q_M(\log(a'b'))P.
\end{aligned}
\tag{3.3}
\]
В частности, при `a=a'` остаются все `b!=b'`, а при `a!=a'` — все межстрочные произведения, включая совпадение `ab=a'b'`. Полный cutoff сохранён для каждого множителя отдельно. Матрицы не предполагаются коммутирующими. Промежуточный `P` не удаляется.

У исходной линейной сборки `S=I+J-K+II` нет квадратных смешанных секторных произведений. Мы не квадратили это четырёхсекторное равенство. Квадратим только (3.2); именно его смешанные члены находятся в (3.3).

## 4. Проверенный механизм: взвешенная энергия с тем же W

**Лемма 3 [ABSTRACT | PAPER].** Для любых положительных скалярных весов `tau_a`, выбранных в одной ячейке, обозначим
\[
Z_\tau=\sum_a\frac{\alpha_a^2}{\tau_a},
\qquad
\mathcal E_\tau=\sum_a\tau_a\mathsf H_a^2.
\]
Тогда
\[
\boxed{\mathrm{II}^2\preceq Z_\tau\mathcal E_\tau.}
\tag{4.1}
\]
Более того, полная потеря имеет точный положительный вид:
\[
\boxed{
Z_\tau\mathcal E_\tau-\mathrm{II}^2
=
\sum_{a<a'}\tau_a\tau_{a'}
\left(
\frac{\alpha_a}{\tau_a}\mathsf H_{a'}
-
\frac{\alpha_{a'}}{\tau_{a'}}\mathsf H_a
\right)^2\succeq0.
}
\tag{4.2}
\]

Это доказывается раскрытием **обоих** порядков каждого матричного произведения. Так смешанные члены не «исчезают»: их цена содержится в выброшенной неотрицательной форме (4.2).

Для настоящего `W`:
\[
\boxed{
|\operatorname{Tr}(W\mathrm{II})|^2
\le\operatorname{Tr}(W\mathrm{II}^2)
\le Z_\tau\operatorname{Tr}(W\mathcal E_\tau).
}
\tag{4.3}
\]
В первой строке используется Коши в матричном скалярном произведении `Tr(W X*Y)`. Один и тот же `W` стоит во всех суммах; нет перехода от среднего фиксированного вектора к адаптивному спектральному максимуму. Множитель размерности не нужен.

Однако это **усиление** односторонней задачи: оно контролирует и большую отрицательную сторону. Полный отрицательный спектр не является долгом исходного потребителя. Пример `II=-K I` показывает различие задач, но не подменяет собой источник CCM.

### 4.1. Законное завершение доступными оценками

Из источникового `||A(n)||<=2`, после полной `b`-сборки:
\[
\|\mathsf H_a\|\le2\mathsf B_a,
\qquad
\mathsf H_a^2\preceq4\mathsf B_a^2P.
\tag{4.4}
\]
Следовательно,
\[
\boxed{
\mathrm{II}\preceq s_m(\tau)P,
\quad
s_m(\tau)=2\sqrt{
\left(\sum_a\frac{\nu_U(a)^2}{a\tau_a}\right)
\left(\sum_a\tau_a\mathsf B_a^2\right)}.
}
\tag{4.5}
\]
Это действительный полный верх для каждого допустимого `W`, но он уже потерял чувствительность к конкретным autocorrelation-значениям внутри строк.

При `tau_a=1` наша арифметическая энергия (2.6) даёт
\[
Z_1\le h_{A_*}h_U^3,
\qquad
\sum_a\mathsf B_a^2
\le36m\sum_{U<a\le A_*}\frac1a
\le36m\log(A_*/U)
\]
при `A_*>U`. Поэтому
\[
\boxed{
s_m(1)\le
12\sqrt m\,h_U^{3/2}\sqrt{h_{A_*}\log(A_*/U)}.
}
\tag{4.6}
\]
При исходном расписании это `O_epsilon(sqrt(m)(log m)^(5/2))`. Никакой положительной степени `U` не заплачено за саму короткую обратную свёртку, но полный показатель всё равно `1/2`.

## 5. Оптимизация ВСЕХ положительных весов: точный лучший бюджет

Не останавливаемся на случайном выборе `tau=1`.

**Теорема 4 [FINITE_CELL | PAPER].** После ровно указанного возврата (4.4),
\[
\boxed{
s_m^*:=\inf_{\tau_a>0}s_m(\tau)
=2\sum_{U<a\le A_*}
\frac{|\nu_U(a)|}{\sqrt a}\,\mathsf B_a.
}
\tag{5.1}
\]

**Доказательство.** Коши в обычных вещественных последовательностях даёт
\[
\left(\sum\alpha_a^2/\tau_a\right)
\left(\sum\tau_a\mathsf B_a^2\right)
\ge\left(\sum|\alpha_a|\mathsf B_a\right)^2.
\]
На активных строках `alpha_a!=0, B_a>0` равенство достигается при
\[
\tau_a=|\alpha_a|/\mathsf B_a.
\]
Строки с нулевой `alpha` или `B` не вносят вклад в исходный оператор; можно удалить их точно либо получить тот же инфимум предельным выбором весов. ∎

Это **не новая факторизация, дающая отмену**, а точное решение задачи оптимизации выбранного верхнего сертификата. В частности, нет смысла запускать численный поиск `tau`, надеясь, что он извлечёт потерянный знак: его лучший ответ известен аналитически.

Поскольку `|nu_U(a)|<=sum_(d|a,d<=U)1`,
\[
\sum_{U<a\le A_*}\frac{|\nu_U(a)|}{a}
\le\sum_{d\le U}\frac1d h_{\lfloor A_*/d\rfloor}
\le h_Uh_{A_*}.
\]
По принятой элементарной цене `W(x)<=6sqrt(x)`,
\[
\boxed{s_m^*\le12\sqrt m\,h_Uh_{A_*}.}
\tag{5.2}
\]
Это `O_epsilon(sqrt(m)(log m)^2)`. Прямая старая оценка полного `S` всё ещё лучше.

## 6. Настоящий арифметический свидетель половинной цены сертификата

**Теорема 5 [COFINAL_FAMILY | PAPER].** При (1.8) существует исходный поздний диапазон, на котором
\[
\boxed{s_m^*\ge\frac{\sqrt m}{32\log m}.}
\tag{6.1}
\]
Она действует на каждой достаточно поздней целой ячейке, а не только на подобранной панели.

**Доказательство.** Положим `x=sqrt(m)/4` и рассмотрим действительные простые
\[
\mathcal P_x=\{p:x<p\le2x\},\qquad N_x=|\mathcal P_x|.
\]
При фиксированном `epsilon<1/32` на позднем диапазоне `U,V<x`. Тогда для всех этих простых
\[
\nu_U(p)=-1.
\tag{6.2}
\]
Это точное значение, не предположение о независимости или статистике Мёбиуса.

Для любых различных `p,q` из этой совокупности имеем `pq<=m/4<m`, поэтому исходная гипербола включает их. Их вклад в правую сторону (5.1) не меньше
\[
2\sum_{\substack{p,q\in\mathcal P_x\\p\ne q}}
\frac{\log q}{\sqrt{pq}}
\ge N_x(N_x-1)\frac{\log x}{x}.
\tag{6.3}
\]
Обычная PNT даёт `N_x~x/log x`; значит, на позднем диапазоне
\[
N_x\ge\frac{x}{2\log x},\qquad N_x-1\ge N_x/2.
\]
Следовательно, (6.3) не меньше
\[
\frac{x}{8\log x}
=\frac{\sqrt m}{32\log x}
\ge\frac{\sqrt m}{32\log m}.
\]
Все остальные члены **этого положительного бюджета** можно не использовать для нижней границы. Они не удаляются из оператора. В частности, proper powers `p^k` остаются во всех исходных формулах. ∎

### 6.1. Какой вывод действительно допустим

Для любого фиксированного `theta<1/2` и `C>0` запас обещанного подполустепенного **сертификата** имеет верхнюю границу
\[
C m^\theta-s_m^*
\le C m^\theta-\frac{\sqrt m}{32\log m}<0
\]
на достаточно позднем диапазоне. Это строгая отрицательная верхняя граница запаса — законное опровержение **этой формы сертификата**. Кофинальный выбор `m` её не обходит.

Но из `s_m^*>=...` **не следует**
\[
\lambda_{\max}(\mathrm{II})\ge...,
\]
поскольку `s_m^*` — верхняя мажоранта, а не измеренный источник. Никакое подобное нижнее спектральное утверждение здесь не сделано.

Теорема не запрещает работать с полной матрицей `E_tau` без (4.4), возвращать положительный дефект (4.2), использовать недиагональную метрику строк или вовсе не квадратить одностороннюю форму. Она не запрещает actual cancellation.

### 6.2. Почему этот свидетель показывает именно потерю нужной информации

Для различных `p,q>max(U,V)` конечная Vaughan-сборка при `n=pq` имеет коэффициенты
\[
I_n=\log p+\log q,\qquad J_n=K_n=0,
\qquad (\mathrm{II})_n=-\log p-\log q.
\tag{6.4}
\]
Их сумма равна настоящему `Lambda(pq)=0`.

Для `p>max(U,V)` и `k>=2`:
\[
I_{p^k}=k\log p,\quad
(\mathrm{II})_{p^k}=-(k-1)\log p,\quad
(I+\mathrm{II})_{p^k}=\log p.
\tag{6.5}
\]
Так все высшие степени простого восстанавливаются с исходным коэффициентом один, а не удаляются вместе с композитами.

**Вся нижняя цена (6.1) уже возникает из различных полупростых произведений, которые в исходном `Lambda` сокращаются точно.** Положительный сертификат забыл этот факт. Это не означает, что короткий оператор `I` целиком имеет большую норму: его собственные внутренние знаковые и геометрические компенсации уже оплачены в S1. Нижняя граница относится к сумме модулей до этих компенсаций.

Итак, «много слагаемых остаётся в энергетическом верхе» не означает «исходная форма велика». Полученный witness как раз различает эти два утверждения.

## 7. Где остановилась попытка

Есть две разные границы, и их нельзя смешивать.

**Первая структурная потеря:** (4.1)–(4.3) усиливают исходную верхнюю задачу до двустороннего квадрата и отбрасывают точную положительную матрицу (4.2). В ней находятся реальные межстрочные зависимости `nu_U(a)` и матричных выходов.

**Первый неоплаченный более сильный арифметический вход:** попытка улучшить фактический
\[
\operatorname{Tr}(W\mathcal E_\tau)
=
\sum_a\tau_a
\sum_{\substack{b,b'>V\\ab\le m,ab'\le m}}
\frac{\Lambda(b)\Lambda(b')}{\sqrt{bb'}}
\operatorname{Tr}\!\left[
W P Q_M(\log(ab))P Q_M(\log(ab'))P
\right]
\tag{7.1}
\]
настолько, чтобы после умножения на `Z_tau` и извлечения корня появилась нужная меньшая степень. Вместо этого реально выведена лишь (4.4), и для всего семейства цен после неё установлено (6.1).

**Оценка (7.1) нужной силы не доказана и не принимается как предпосылка.** Она также не объявляется необходимой для исходного потребителя. Простое назначение её новым именем не меняет математический долг.

Новый LCM-контроль из §2 оценивает энергию коэффициентов, но не доказывает малость (7.1) и не даёт знака для (1.6). Подставить скалярную `q_U` вместо полного матричного веса означало бы потерять зависимость от `a`, истинную гиперболу и смешанные Fourier-координаты.

В выполненной попытке RH, ZF78, Mertens-strength bounds, strong variance или искомая signed-корреляция не импортировались. Сильная конечная неопределённость не маскируется обещанием внешнего поставщика.

## 8. Полный возврат к исходной CCM

**[COFINAL_FAMILY | PAPER — принятые короткие входы S1, с полным новым возвратом.]** Обозначим
\[
\mathfrak b_m=40+16\Omega,\qquad
\mathfrak c_m=12+4\Omega,
\]
\[
B_{\rm short}
=2\mathfrak b_m\sqrt U+12\sqrt V
+12\mathfrak c_m\sqrt{UV}.
\tag{8.1}
\]
S1 поставляет точно
\[
S_m=I+J-K+\mathrm{II},\qquad
\|I\|+\|J\|+\|K\|\le B_{\rm short}.
\]
В частности,
\[
-B_{\rm short}P\preceq S_m-\mathrm{II}\preceq B_{\rm short}P.
\tag{8.2}
\]

Полученный механизм поэтому даёт **полный действительный верх**
\[
\boxed{S_m\preceq(s_m^*+B_{\rm short})P.}
\tag{8.3}
\]
При (1.8) `B_short=O_epsilon(m^(2epsilon)/log m)` на достаточно позднем диапазоне; менее острая `O_epsilon(m^(2epsilon))` также достаточна. Но (6.1) и (5.2) оставляют для всего сертификата половинную степень.

Пусть
\[
D_m=P(A_{\rm arch}-c_AI)P,\qquad\|D_m\|\le50L+8.
\]
Тогда
\[
PK_mP=D_m-S_m
\succeq D_m-(s_m^*+B_{\rm short})P,
\]
\[
\boxed{
PK_mP\succeq-
[s_m^*+B_{\rm short}+50L+8]P.
}
\tag{8.4}
\]
Это restricted-floor на исходной полосе, не full-SP.

Для отдельного исходного `T_{>R}=S_m-T_{<=R}`:
\[
T_{>R}\preceq(s_m^*+B_{\rm short})P-T_{\le R}.
\]
Только если нужен скалярный верх, добавляется один раз
\[
b_{\rm small}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\tag{8.5}
\]
В (8.4) эта отдельная плата не начисляется. Q02 `T-V` не используется: мы работали прямо с полным `S` и только потом с `T`; неоплаченный Suzuki-дефект не возвращался как дополнительная обязательная задача.

### 8.1. Сравнение с уже имеющимся источником

Старый элементарный полный верх
\[
\boxed{S_m\preceq12\sqrt m\,P}
\tag{8.6}
\]
сильнее завершённой (8.3). Его можно оставить как фактический безусловный fallback:
\[
PK_mP\succeq-[12\sqrt m+50L+8]P,
\qquad
T_{>R}\preceq12\sqrt mP-T_{\le R}.
\]
Не следует приписывать (8.6) новой Vaughan-оценке. Аналогично, из (8.2) и старого полного двухстороннего элементарного конверта можно получить `||II||<=12sqrt(m)+B_short`; это обратное использование уже известного `S`, а не новое улучшение `S` через `II`.

| Результат | Полный показатель | Статус |
|---|---:|---|
| Три коротких сектора S1 | `2epsilon` | Принятый оплаченный возврат, не full bound |
| Короткая обратная coefficient-energy §2 | Только логарифмы | Новый в этой попытке проверенный вспомогательный расчёт |
| Завершённый weighted-energy/row-cap сертификат | `1/2` с логарифмами | Доказан, но не улучшает старый верх |
| Старый прямой элементарный `S` | `1/2` | Сохранён без улучшения |
| Принятый Q03/S12 | `3/8` | **CONDITIONAL на ZF78**, здесь не использован |
| Новая `theta(epsilon)->0` для II | — | **Не доказана** |

## 9. Содержательный откат и один следующий discriminator

### 9.1. Что прекращаем

Останавливается не Vaughan-тождество как таковое и не арифметический маршрут, а семейство

`короткая Möbius-energy → weighted Cauchy → независимые положительные цены строк → оптимизация весов`.

Для него теперь есть аналитический оптимум (5.1) и источникозависимая нижняя цена (6.1). Улучшать постоянные в `q_U`, считать больше строк или обучать веса `tau` для этого семейства бессмысленно в отношении искомой степени.

### 9.2. Куда именно возвращаемся

Выбранный откат — **до квадрата и, если нужная связь уже потеряна при выделении II, до четырёхсекторной оплаты**, к линейному полному `S` с коэффициентами, собранными по исходному произведению `n`.

Причина не философская: семейство (6.4) показывает, что доказанная половинная плата выбранного сертификата возникает на композитах с точно нулевым суммарным исходным коэффициентом. Будущий механизм должен использовать их реальную компенсацию до положительной оплаты, а не лишь объявлять низкую норму коэффициентного квадрата.

Это **не новая поставленная signed-оценка**. Нужного нового неравенства для ранней формы в Q15 не получено. В частности, здесь не запускается Q16 с новым названием (7.1).

### 9.3. Отличающий математический тест

**Выбран ровно один следующий discriminator: rough-semiprime return test.** Для любого предложенного нового совместного верхнего сертификата проверить сначала его полный возврат на буквальных коэффициентных пакетах
\[
\begin{array}{ll}
n=pq,\ p\ne q>\max(U,V):&
(\log p+\log q)+(-\log p-\log q)=0,\\[2mm]
n=p^k,\ p>\max(U,V):&
k\log p-(k-1)\log p=\log p.
\end{array}
\tag{9.1}
\]
Тестировать нужно с **одним** неизменённым `A(n)` и `W`, а не только в таблице модулей коэффициентов. Нулевой composite-пакет как оператор равен нулю для всех допустимых `W`; proper powers остаются.

Не всякий допустимый верх обязан буквально равняться нулю на нулевом объекте. Но если его полный бюджет вновь начисляет необратимую плату `>=c sqrt(m)/log m` только за эти нулевые packets, такой сертификат не даст sub-half-power без отдельно доказанного возврата этой платы. Это дешёвый проверяемый фильтр **цены**, а не запрет всех способов доказательства.

### 9.4. Две сохранённые координаты фронта — не две новые программы

| Представление | Что остаётся совместным | Kill-power / стоимость | Решение |
|---|---|---|---|
| Прямой `Tr(W S)` с productwise точной свёрткой и непрерывным центрированием S4 | Все source-компенсации и только нужная верхняя сторона | Высокая для теста (9.1); низкая алгебраическая цена, новый знак неизвестен | **Выбранный откат** |
| Полный `(4.2)` вместе с `E_tau`, до удаления положительного дефекта | Матричные корреляции строк, обе стороны после квадрата | Средняя диагностическая сила; более сильный долг, высокая цена его оценки | Сохранить как проверку, не назначать обязательным supplier |

Ни одна строка таблицы не утверждает наличие доказанного нового источникового неравенства.

## 10. Проверки и их точные ограничения

Регистрация сделана **после чтения и предварительного PAPER-расчёта, до новых исполняемых проверок**. Это не прогноз открытия задним числом. Файл регистрации включён полностью.

1. Источниковый S2 воспроизведён без изменения: **8192** точных формально-логарифмических коэффициентных случая; JSON совпал с S3. Это воспроизведение старого теста, не 8192 новых доказательства.
2. Новый проверяющий завершил **7801** локальный exact control. Он проверяет short inverse, обе Type-II сборки, LCM/floor/harmonic identities, totient-квадраты, полную некоммутативную цену Коши, оптимизацию весов и семипростые/proper-power packets.
3. Выполнены **3** неинтервальные диагностики при **50 десятичных знаках**: исходный `Q`, все три контакта `P`, полная Vaughan-сборка, та же rank-one `W`, смешанные квадраты и точное autocorrelation-представление.

Численные ячейки `(m,M)=(16,2),(64,3),(125,4)` — **только конечные проверки нормировки общих тождеств**, не поздний режим фиксированного `epsilon<1/32`. Они не используются для получения любой асимптотической степени. Значения Rayleigh в JSON не сертификаты знака; полные спектры CCM не считались.

**Неудачный запуск сохранён.** В самом конце первого exact-run была ошибочно добавлена проверка `nu_2(4)=1`. На самом деле `nu_2(4)=mu(4)=0`. Исправленный threshold-контроль — `nu_3(6)=1`; квадратный нуль `nu_2(4)=0` оставлен отдельно. Это ошибка ожидания дополнительного теста, не дефект доказанных формул. Первый запуск не считается проходом, журнал включён. P5 не получает ретроактивной отметки «первый запуск прошёл».

Новые exact-матрицы в абстрактных тестах — рациональные контрольные матрицы, не реальные CCM. Доказательства ко-финальной нижней цены §6 и отсутствия новой степени находятся в тексте, не в конечных данных.

**Arb=0; Lean=0; независимый аудит нового вывода не запускался.** Использованы стандартный Python и имеющийся `mpmath 1.3.0`, без установки пакетов. Финальный Markdown проверен повторным извлечением и запуском встроенных скриптов; результаты совпали с включёнными JSON.

## 11. Ledger, зависимости и closeout

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| SRC | Буквальные source/receiver S1,S4–S7 | COFINAL_FAMILY | PAPER | Приняты в указанных областях, не новый upstream-аудит |
| A1 | Short-inverse floor/harmonic LCM formulas | FINITE_CELL | PAPER | Доказаны |
| A2 | Totient diagonalization и bounds (2.4) | FINITE_CELL | PAPER | Доказаны; не signed-II bound |
| B1 | Полная матричная сборка и positive Cauchy loss (4.2) | ABSTRACT | PAPER | Доказаны |
| B2 | Weighted row certificate (4.5) и его точный оптимум | FINITE_CELL | PAPER | Доказаны |
| B3 | Нижняя половинная цена этого оптимума | COFINAL_FAMILY | PAPER | Доказана с обычной PNT |
| B4 | Actual spectrum II имеет половинную нижнюю цену | COFINAL_FAMILY | CONDITIONAL | **Не утверждается и не доказано** |
| C1 | Полный возврат (8.3)–(8.5) | COFINAL_FAMILY | PAPER | Доказан; новая полная степень отсутствует |
| C2 | Старый Q03 `3/8` | COFINAL_FAMILY | CONDITIONAL | Только сравнение; прежняя ZF78 |
| O1 | Требуемая one-sided actual-II/CCM оценка | COFINAL_FAMILY | CONDITIONAL | OPEN; не вход новых лемм |
| T1 | 7801 exact и 3 неинтервальных случая | FINITE_CELL | PAPER | Контроль реализации, не глобальный знак |

### K8A: неизменённый потребитель и граница отрицательного результата

- **DOWNSTREAM_CONSUMER:** отдельный sparse-band adverse-witness receiver исходной полной CCM, S6–S7.
- **ACTUAL_CONSUMER_REQUIREMENT:** `PK_mP >= -C_epsilon m^eta(epsilon)P`, `eta(epsilon)->0`, либо достаточная общая для всех векторов ко-финальная версия. Не требуется full-SP или отдельно малая абсолютная норма каждой строки.
- **ORIGINAL_REQUESTED_OBJECT:** joint upper для настоящей II; выбранный способ — коэффициентная LCM-energy и её матричный возврат.
- **ORIGINAL_OBJECT_IS:** `NOT_NECESSARY` для отдельно квадратичного/row-cap сертификата. Сама II эквивалентна полному S **с точной платой (8.2)**; это не делает наш способ её оценки обязательным.
- **KNOWN_WEAKER_INTERFACES:** прямая односторонняя (1.6); прямой S-upper; direct Q-floor; сохранение полного матричного дефекта (4.2) вместо независимых цен.
- **FAILURE_TYPE:** `NO_DERIVATION` для actual signed arithmetic; `INCOMPATIBILITY` для обещанного sub-half-power **после** (4.4).
- **EPISTEMIC_STATUS:** `RESEARCH_DEBT` для основной задачи; `MATHEMATICALLY_DEAD` лишь для сертификата §5–6.
- **KILL_SCOPE:** `THEOREM_SHAPE`, не `ROUTE_FAMILY`.
- **KILL_EVIDENCE:** (5.1) и (6.1), реальные `nu_U(p)=-1`, `Lambda(q)=log q`, исходная гипербола, отрицательный верх запаса в §6.1.
- **REOPEN_TRIGGER:** источникозависимый направленный контроль до (4.4) или до (4.1), с полной платой, использующий информацию, потерянную этими неравенствами.
- **NOVELTY_AXIS:** в этой попытке проверена арифметическая short-inverse energy и исключено целое оптимизируемое семейство её грубых переносов. Ни литературный приоритет, ни новая CCM-степень не заявляются.

### Три структурные проверки до объявления долга

**FORM_IDENTITY:** переход из свёртки к LCM/totient-квадрату точен, но контролирует coefficient-energy, не joint form. **VANISHING IDENTITY:** exact semiprime/proper-power cancellation (6.4)–(6.5) работает до положительной оплаты; выбранный сертификат её не сохраняет. **COLLAPSE OBJECT:** полная матричная положительная разность (4.2) могла бы компенсировать row-energy, но независимого количественного сравнения не получено. Она не назначается новым обязательным theorem.

### Fate прогнозов

P1–P4 подтверждены письменными выводами и соответствующими конечными контролями. P5 обнаруживает намеренно испорченные mixed/cutoff/LCM шаги; дополнительно сам проверяющий остановился на неверном ожидании `nu_2(4)=1`, что записано отдельно. P6 подтверждён тремя неинтервальными тестами только как нормировочная диагностика. Глобальная степенная малость не предсказывалась и не получена.

```yaml
MEMORY_ENTRY:
  iteration: CCM_VAUGHAN_JOINT_Q15_2026_10_24
  target: ACTUAL_ONE_SIDED_TYPE_II_ON_ORIGINAL_P
  status: OPEN
  failed_strategy: Short-inverse coefficient square followed by weighted Cauchy and independent row caps
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: Actual rough semiprimes already force half-power in the optimized absolute certificate although their total source Lambda coefficient is zero
  forbidden_future_move: Optimize scalar row weights or improve the coefficient LCM constant and call that a new CCM power
  next_decisive_test: Productwise semiprime/proper-power return of a candidate before independent positive payments
  current_smallest_missing_information: Signed coupling in (1.6) lost at (4.1)/(4.4); no new mandatory supplier named
  consumer_power_progress: NONE
  route_score: 4_for_precise_certificate_falsification_not_for_RH_progress
  route_family_death: NOT_ESTABLISHED
```

## 12. Ровно одна CODEX DIRECTIVE

**Выполнить ограниченный независимый PAPER-аудит этого Q15, а не запускать новый поиск весов.** Проверить конечные LCM/harmonic формулы, exact noncommutative defect (4.2), оптимум (5.1), фактическую rough-semiprime нижнюю цену (6.1) и возврат (8.2)–(8.5). Воспроизвести встроенные exact-тесты; отдельно сверить, что исходный квадратный нуль `nu_2(4)=0` не заменён единицей. Выдать первую ошибку либо приёмку **ровно этих** утверждений. Не принимать из этого знак actual II, новую степень, RH, full-SP; не создавать автоматический Q16. Следующий новый механизм пропускать только после productwise discriminator (9.1) и расчёта полной цены.

## 13. Первичные внешние сведения и граница использования

1. **NIST DLMF §27.5**, формулы 27.5.2, 27.5.4, 27.5.5: нормировки Möbius-инверсии, `sum_(d|n)phi(d)=n`, `Lambda=mu*log`. Конечные identities §2–6 доказаны в тексте, а не импортированы в виде необоснованного signed bound.
2. **NIST DLMF §27.12**, 27.12.5: обычная безусловная PNT; из неё для §6 используется только `pi(2x)-pi(x)~x/log x`. Не использованы 27.12.7 (RH-эквивалентная точность), zero-density гипотеза, короткие интервалы растущей относительной узости или uniform-Mertens.

```text
https://dlmf.nist.gov/27.5
https://dlmf.nist.gov/27.12
```

Точные опоры из приложенного запроса: начало L1–54 — текущее поручение; S1 L132–272 — конечный Vaughan и короткий возврат; S4 — полный continuous rank-two input; S5 — прежний full-k и цена квадратов; S6–S7 — тот же receiver; S8–S12 — уже принятые границы и причины не повторять прежние импорты. Исторические статусы не заменяют текущий результат.

---

## Приложения: полная воспроизводимость

Ниже включены исходные файлы **этого** проверяющего и фактические результаты. Они не являются ещё одним математическим поставщиком. Для exact-проверки сохранить `registration.json` и `check_q15.py` в один каталог и выполнить `python3 check_q15.py`: подстановок переменных и сторонних библиотек не требуется. Диагностика использует `mpmath 1.3.0`; при уже установленном пакете — `python3 diagnostic_q15.py`. Для отдельного окружения с uv: `uv run --with mpmath==1.3.0 python diagnostic_q15.py`. Это команда воспроизведения, не заявка на выполненную здесь установку.

Имена файлов в маркерах `FILE_BEGIN`/`FILE_END` точные; относительный путь `source_replay/check.py` означает подкаталог внутри выбранного рабочего каталога, не путь репозитория. JSON содержит собственные хеши скриптов, поэтому при копировании надо сохранять UTF-8 и конечный LF.

### Манифест принятых 12 источников

```json
[
  {
    "id": "S1",
    "path": "docs/literature/openai_math_2026-10-07/CCM_Q15_VAUGHAN_JOINT_BUDGET.md",
    "bytes": 7127,
    "sha256": "1e13f0487d1a3362817e34112c11953a7296c18bd3500b31995aa221d540bf41"
  },
  {
    "id": "S2",
    "path": "docs/literature/openai_math_2026-10-07/q15_vaughan_checks/check.py",
    "bytes": 1441,
    "sha256": "f3757ee4e2854e20faf66585b4aead35e995132b5b2e46938fde88cb79447430"
  },
  {
    "id": "S3",
    "path": "docs/literature/openai_math_2026-10-07/q15_vaughan_checks/results.json",
    "bytes": 268,
    "sha256": "24cee3039b0e01d4ed40f193e149d6c9c87221d5a05b5e923ff9d14832d86016"
  },
  {
    "id": "S4",
    "path": "docs/literature/openai_math_2026-10-07/CCM_CONTINUOUS_RANK_TWO_TEST.md",
    "bytes": 3751,
    "sha256": "6c917626df5d97fae5df2cc4a5b409465e23753de2c38e7b41d47e66f0eecbe1"
  },
  {
    "id": "S5",
    "path": "docs/literature/openai_math_2026-10-07/PROSHKA_CCM_ACTUAL_MOBIUS_JOINT_Q01_VERDICT_2026-10-20.md",
    "bytes": 61446,
    "sha256": "f072574fc3c138be50ba683e3c21cdf66d5c0078ec160fcf212349f356b0b43e"
  },
  {
    "id": "S6",
    "path": "docs/literature/openai_math_2026-10-07/CCM_SPARSE_BAND_RECEIVER.md",
    "bytes": 6174,
    "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06"
  },
  {
    "id": "S7",
    "path": "docs/literature/openai_math_2026-10-07/CCM_RESTRICTED_PRIME_RECEIVER.md",
    "bytes": 9606,
    "sha256": "2b7b3040a510f5133049b358e81a922a83bc1439ab77222b9520a7ca5e349acd"
  },
  {
    "id": "S8",
    "path": "docs/literature/openai_math_2026-10-07/CCM_Q14_CONCLUSION.md",
    "bytes": 3926,
    "sha256": "e4203844a9143b0bfe05de99cea660449fa2f44aeee7031e13b8ef78f9427e64"
  },
  {
    "id": "S9",
    "path": "docs/literature/openai_math_2026-10-07/CCM_LOCAL_BLOCK_Q08_CONCLUSION.md",
    "bytes": 4468,
    "sha256": "9368311f705db6c1052f8b017312886d162f7b7bd9c6597afbc2975188f29817"
  },
  {
    "id": "S10",
    "path": "docs/literature/openai_math_2026-10-07/CCM_Q11_MOBIUS_PAIR_RETURN.md",
    "bytes": 4597,
    "sha256": "0401fbcbb5da07991907d781ac7d9c73246e48739b74d611254304a60812c75d"
  },
  {
    "id": "S11",
    "path": "docs/literature/openai_math_2026-10-07/CCM_C5_CANCELLATION_LITERATURE_AUDIT.md",
    "bytes": 10195,
    "sha256": "98873e8e4b4cdf08fee021e921ed672653a4af088be6f63958874695042ef312"
  },
  {
    "id": "S12",
    "path": "docs/literature/openai_math_2026-10-07/CCM_JOINT_Q03_CONCLUSION.md",
    "bytes": 3890,
    "sha256": "e93cceee8fc889f94e8235451caa5761790e49c0fd441b5a15180b222aba35ad"
  }
]
```

### `registration.json`

<!-- FILE_BEGIN: registration.json -->
```json
{
  "phase": "Q15",
  "timing": "After source reading and paper derivation; before new executable checks. Not a prediction of an undiscovered theorem.",
  "predictions": [
    {"id":"P1","claim":"Finite Vaughan, two Type-II coefficients and short-inverse identity agree atom by atom, with all proper prime powers and exact cutoffs."},
    {"id":"P2","claim":"The nu_U coefficient square has the exact floor/LCM and totient-square factorizations; lower and upper rational bounds pass."},
    {"id":"P3","claim":"Full matrix square includes mixed rows and mixed prime factors; weighted Cauchy holds without commuting projected kernels."},
    {"id":"P4","claim":"The positive-row-weight optimization gives exactly the absolute row certificate, not an arithmetic power gain."},
    {"id":"P5","claim":"Deleting a mixed product, a hyperbolic boundary, or proper-power contributions is detected by planted finite tests."},
    {"id":"P6","claim":"Small actual-kernel diagnostics preserve original P and Vaughan recombination; they are not asymptotic or interval certificates."}
  ],
  "no_prediction": "No new full CCM exponent, no sign of actual II, no numerical proof of the cofinal certificate lower bound."
}
```
<!-- FILE_END: registration.json -->

### `check_q15.py`

<!-- FILE_BEGIN: check_q15.py -->
```python
"""Exact finite controls for the Q15 paper calculation; not CCM sign certificates."""
from fractions import Fraction as F
from collections import Counter
from math import gcd, isqrt
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
stats = Counter()
N = 160
fac = [Counter() for _ in range(N+1)]
for n in range(2,N+1):
    z=n
    for p in range(2,isqrt(n)+2):
        while z%p==0:
            fac[n][p]+=1; z//=p
    if z>1: fac[n][z]+=1
mu = [0]+[0 if any(e>1 for e in fac[n].values()) else (-1)**len(fac[n]) for n in range(1,N+1)]
phi=[0]+[sum(gcd(j,n)==1 for j in range(1,n+1)) for n in range(1,N+1)]
lam = [Counter({next(iter(fac[n])):1}) if len(fac[n])==1 else Counter() for n in range(N+1)]

def clean(c): return {k:v for k,v in c.items() if v}
def add(out, c, a=1):
    for p,e in c.items(): out[p]+=a*e

def nu(n,U): return sum(mu[d] for d in range(U+1,n+1) if n%d==0)
def sig(n,U): return sum(mu[d] for d in range(1,min(U,n)+1) if n%d==0)
def lcm(a,b): return a*b//gcd(a,b)
def harm(n): return sum((F(1,j) for j in range(1,n+1)), F())

# Complete actual arithmetic and both Type-II parenthesizations.
for U in range(1,9):
    for n in range(1,N+1):
        assert nu(n,U)==(1 if n==1 else 0)-sig(n,U)
        if n<=U: assert nu(n,U)==0
        stats['short_inverse_coefficients']+=1
    for V in range(1,9):
        for n in range(1,97):
            left=Counter();right=Counter()
            for d in range(U+1,n+1):
                if n%d: continue
                v=n//d
                for k in range(V+1,v+1):
                    if v%k==0:add(left,lam[k],mu[d])
            for a in range(U+1,n+1):
                if n%a==0 and n//a>V:add(right,lam[n//a],nu(a,U))
            assert clean(left)==clean(right)
            stats['two_typeII_coefficients']+=1

# Exact LCM energy, signed floor error and harmonic energy.
for U in range(1,17):
    Q=sum((F(mu[d]*mu[e],lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1)),F())
    y={r:sum((F(mu[d],d) for d in range(r,U+1,r)),F()) for r in range(1,U+1)}
    G=sum((F(mu[r]**2,phi[r]) for r in range(1,U+1)),F())
    assert Q==sum((phi[r]*y[r]**2 for r in y),F())
    assert sum((mu[r]*y[r] for r in y),F())==1
    assert Q*G>=1 and G<=3*harm(U) and Q<=harm(U)**3
    stats['totient_diagonalization_and_bounds']+=1
    for X in (U,2*U,3*U,5*U):
        exact=sum(nu(a,U)**2 for a in range(U+1,X+1))
        count=sum(mu[d]*mu[e]*(X//lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1))-1
        assert exact==count and abs(F(exact+1)-X*Q)<=U**2
        zh=sum((F(nu(a,U)**2,a) for a in range(U+1,X+1)),F())
        rhs=sum((F(mu[d]*mu[e],lcm(d,e))*harm(X//lcm(d,e)) for d in range(1,U+1) for e in range(1,U+1)),F())-1
        assert zh==rhs and zh<=harm(X)*harm(U)**3
        stats['floor_and_harmonic_LCM']+=1

# Algebraic matrix controls use rational matrices, NOT numerical CCM matrices.
def zero():return ((F(0),F(0)),(F(0),F(0)))
def plus(A,B):return tuple(tuple(A[i][j]+B[i][j] for j in range(2)) for i in range(2))
def times(s,A):return tuple(tuple(s*x for x in row) for row in A)
def prod(A,B):return tuple(tuple(sum(A[i][k]*B[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def total(xs):
    o=zero()
    for x in xs:o=plus(o,x)
    return o

def psd(A):return A[0][1]==A[1][0] and A[0][0]>=0 and A[1][1]>=0 and A[0][0]*A[1][1]>=A[0][1]**2
for z in range(1,17):
    mats=[((F(j+z,3),F((-1)**j,2)),(F((-1)**j,2),F(2*j-z,5))) for j in range(1,5)]
    alpha=[F((-1)**(z+j)*(j+1),j+2) for j in range(4)]
    tau=[F(j+z+1,j+2) for j in range(4)]
    T=total(times(a,A) for a,A in zip(alpha,mats))
    Z=sum(a*a/t for a,t in zip(alpha,tau))
    G=total(times(t,prod(A,A)) for t,A in zip(tau,mats))
    gap=plus(times(Z,G),times(-1,prod(T,T)))
    squares=[]
    for i in range(4):
        for j in range(i+1,4):
            R=plus(times(alpha[i]/tau[i],mats[j]),times(-alpha[j]/tau[j],mats[i]))
            squares.append(times(tau[i]*tau[j],prod(R,R)))
    assert gap==total(squares) and psd(gap)
    expansion=total(times(alpha[i]*alpha[j],prod(mats[i],mats[j])) for i in range(4) for j in range(4))
    assert expansion==prod(T,T)
    stats['full_noncommutative_weighted_square']+=1
    B=[F(j+z+2,j+1) for j in range(4)]
    opttau=[abs(a)/b for a,b in zip(alpha,B)]
    cost=sum(abs(a)*b for a,b in zip(alpha,B))
    assert sum(a*a/t for a,t in zip(alpha,opttau))*sum(t*b*b for t,b in zip(opttau,B))==cost**2
    assert sum(a*a/t for a,t in zip(alpha,tau))*sum(t*b*b for t,b in zip(tau,B))>=cost**2
    stats['optimal_row_weight_certificate']+=1

# Exact prime-composite cancellation and all higher powers.
primes=[p for p in range(2,N+1) if fac[p]==Counter({p:1})]
for U in range(1,6):
  V=U
  for p in primes:
    if p<=U:continue
    for q in primes:
      if q<=V or p*q>N:continue
      n=p*q;co=Counter()
      for a in range(U+1,n+1):
        if n%a==0 and n//a>V:add(co,lam[n//a],nu(a,U))
      expected=Counter()
      if p==q:expected[p]=-1
      else:expected[p]-=1;expected[q]-=1
      assert clean(co)==clean(expected)
      totalcoef=Counter();add(totalcoef,fac[n]);add(totalcoef,co)
      assert clean(totalcoef)==clean(lam[n])
      stats['actual_rough_semiprime_and_square']+=1
  for p in primes:
    if p<=U:continue
    n=p*p;k=2
    while n<=N:
      co=Counter()
      for a in range(U+1,n+1):
        if n%a==0 and n//a>V:add(co,lam[n//a],nu(a,U))
      assert clean(co)=={p:-(k-1)}
      stats['proper_power_multiplicity']+=1
      n*=p;k+=1

# Planted errors must be rejected. No positive/negative actual CCM assertion.
I=((F(1),F(0)),(F(0),F(1)))
assert not psd(plus(times(2,I),times(-4,I)))
stats['planted_missing_mixed_row']=1
P=((F(1),F(0)),(F(0),F(0))); A=((F(0),F(1)),(F(1),F(0)))
assert prod(prod(P,prod(A,A)),P)!=prod(prod(prod(P,A),P),prod(A,P))
stats['planted_missing_intermediate_projection']=1
assert sig(6,2)==0 and sig(6,2)**2!=sum(mu[d]**2 for d in (1,2))
stats['planted_discarded_Mobius_cross']=1
assert lcm(2,2)!=2*2
stats['planted_wrong_LCM']=1
# m=20,U=V=2 contains (a,b)=(3,3), not (a,b)=(3,9).
assert 3*3<=20 and not 3*9<=20 and nu(3,2)*lam[9][3]!=0
stats['planted_rectangular_cutoff']=1
assert nu(6,3)==1 and nu(9,2)==-1 and nu(4,2)==0
stats['planted_missing_threshold_and_power']=1

out={"status":"PASS_EXACT_LOCAL_CONTROLS_NOT_CCM_SIGN", "counts":dict(stats),
     "total_checks":sum(stats.values()),"source_spectrum_computed":False,
     "arb_runs":0,"lean_runs":0,
     "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
     "registration_sha256":hashlib.sha256((ROOT/'registration.json').read_bytes()).hexdigest()}
(ROOT/'exact_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```
<!-- FILE_END: check_q15.py -->

### `exact_results.json`

<!-- FILE_BEGIN: exact_results.json -->
```json
{
  "status": "PASS_EXACT_LOCAL_CONTROLS_NOT_CCM_SIGN",
  "counts": {
    "short_inverse_coefficients": 1280,
    "two_typeII_coefficients": 6144,
    "totient_diagonalization_and_bounds": 16,
    "floor_and_harmonic_LCM": 64,
    "full_noncommutative_weighted_square": 16,
    "optimal_row_weight_certificate": 16,
    "actual_rough_semiprime_and_square": 229,
    "proper_power_multiplicity": 30,
    "planted_missing_mixed_row": 1,
    "planted_missing_intermediate_projection": 1,
    "planted_discarded_Mobius_cross": 1,
    "planted_wrong_LCM": 1,
    "planted_rectangular_cutoff": 1,
    "planted_missing_threshold_and_power": 1
  },
  "total_checks": 7801,
  "source_spectrum_computed": false,
  "arb_runs": 0,
  "lean_runs": 0,
  "script_sha256": "324ff678dec441a28d90d5bdd34f46d7b536596f4c05db3956d9f120c9e77bb5",
  "registration_sha256": "03abcd79725f1b5d36f92c193b1ca17884d186947ef43168fe3b7d99d203840b"
}
```
<!-- FILE_END: exact_results.json -->

### `failed_control.json`

<!-- FILE_BEGIN: failed_control.json -->
```json
{
  "run": 1,
  "outcome": "STOPPED_AT_BAD_EXTRA_TEST_EXPECTATION",
  "assertion": "nu(4,2)==1 and nu(9,2)==-1",
  "actual": "nu(4,2)=mu(4)=0; nu(6,3)=mu(6)=1",
  "correction": "Use nu(6,3)==1; retain nu(4,2)==0 as squareful control.",
  "scope": "Mistake in an extra test expectation, not a theorem or source identity; first run not counted as a pass."
}
```
<!-- FILE_END: failed_control.json -->

### `diagnostic_q15.py`

<!-- FILE_BEGIN: diagnostic_q15.py -->
```python
"""Noninterval finite CCM identity diagnostics. No spectral or cofinal certificate."""
from pathlib import Path
from collections import Counter
import hashlib,json
import mpmath as mp
mp.mp.dps=50
ROOT=Path(__file__).resolve().parent

def factor(n):
    out=Counter(); p=2
    while p*p<=n:
        while n%p==0:out[p]+=1;n//=p
        p+=1
    if n>1:out[n]+=1
    return out

def mu(n):
    q=factor(n)
    return 0 if any(e>1 for e in q.values()) else (-1)**len(q)

def mang(n):
    q=factor(n)
    return mp.log(next(iter(q))) if len(q)==1 else mp.mpf(0)

def nu(n,U):return sum(mu(d) for d in range(U+1,n+1) if n%d==0)
def inn(x,y):return sum(mp.conj(x[i])*y[i] for i in range(len(x)))
def mx(A):return max(abs(v) for v in A)
def rel(A,B):return mx(A-B)/(1+mx(A)+mx(B))
rows=[]
for m,M,U,V in [(16,2,2,2),(64,3,2,3),(125,4,3,4)]:
    L=mp.log(m);js=list(range(-M,M+1)); d=len(js)
    w=[2*mp.pi*j/L for j in js]
    C=mp.matrix(d,3)
    for i in range(d):
        C[i,0]=1/mp.sqrt(d)
        C[i,1]=1/(mp.sqrt(L)*(mp.mpf('.5')-1j*w[i]))
        C[i,2]=1/(mp.sqrt(L)*(mp.mpf('.5')+1j*w[i]))
    P=mp.eye(d)-C*(C.H*C)**-1*C.H
    v=mp.matrix([mp.mpc((j+M+1)**2,(-1)**j*(j+M+2)) for j in js]);c=P*v;c/=mp.sqrt(inn(c,c))
    kernels={}
    for n in range(1,m+1):
        s=mp.log(n);Q=mp.matrix(d)
        for r,j in enumerate(js):
            for t,k in enumerate(js):
                Q[r,t]=2*(1-s/L)*mp.cos(w[r]*s) if j==k else (mp.sin(w[t]*s)-mp.sin(w[r]*s))/(mp.pi*(j-k))
        kernels[n]=P*Q*P
    S=mp.matrix(d);I=mp.matrix(d);J=mp.matrix(d);K=mp.matrix(d);II0=mp.matrix(d)
    for n in range(1,m+1):
        an=kernels[n]/mp.sqrt(n)
        S+=mang(n)*an
        if n<=V:J+=mang(n)*an
        for a in range(1,n+1):
            if n%a:continue
            k=n//a
            if a<=U:
                I+=mu(a)*mp.log(k)*an
                for b in range(2,min(V,k)+1):
                    if k%b==0:K+=mu(a)*mang(b)*an
            else:
                bv=sum(mang(b) for b in range(V+1,k+1) if k%b==0)
                II0+=mu(a)*bv*an
    II=mp.matrix(d);H=[];alpha=[];caps=[]
    for a in range(U+1,m//(V+1)+1):
        aa=nu(a,U)/mp.sqrt(a)
        if not aa:continue
        Ha=mp.matrix(d);cap=mp.mpf(0)
        for b in range(V+1,m//a+1):
            lb=mang(b)/mp.sqrt(b)
            Ha+=lb*kernels[a*b];cap+=lb
        if not cap:continue
        H.append(Ha);alpha.append(aa);caps.append(cap);II+=aa*Ha
    vec=[Ha*c for Ha in H]
    vecsum=mp.matrix(d,1)
    for aa,z in zip(alpha,vec):vecsum+=aa*z
    fullmixed=sum(alpha[i]*alpha[j]*inn(vec[i],vec[j]) for i in range(len(H)) for j in range(len(H)))
    omitted=sum(alpha[i]**2*inn(vec[i],vec[i]) for i in range(len(H)))
    cert=2*sum(abs(aa)*b for aa,b in zip(alpha,caps))
    tau=[abs(aa)/b for aa,b in zip(alpha,caps)]
    Z=sum(aa**2/t for aa,t in zip(alpha,tau))
    energy=sum(t*inn(z,z) for t,z in zip(tau,vec))
    gaps=[rel(S,I+J-K+II),rel(II,II0),abs(fullmixed-inn(vecsum,vecsum))/(1+abs(fullmixed))]
    assert max(gaps)<mp.mpf('1e-43')
    assert mx(C.H*c)<mp.mpf('1e-43')
    assert mp.re(Z*energy-inn(vecsum,vecsum))>-mp.mpf('1e-40')
    assert abs(fullmixed-omitted)>mp.mpf('1e-12')
    def f(t):return sum(c[j]*mp.exp(1j*w[j]*t) for j in range(d))/mp.sqrt(L)
    n=3;s=mp.log(n)
    overlap=2*mp.re(mp.quad(lambda t:mp.conj(f(t))*f(t+s),[0,L-s]))
    sourceform=mp.re(inn(c,kernels[n]*c))
    err=abs(overlap-sourceform)
    assert err<mp.mpf('1e-43')
    rows.append({'m':m,'M':M,'U':U,'V':V,
       'schedule':'FINITE_KERNEL_IDENTITY_DIAGNOSTIC_NOT_LATE_FIXED_SMALL_EPSILON',
       'constraint_residual':mp.nstr(mx(C.H*c),10),
       'max_reassembly_residual':mp.nstr(max(gaps),10),
       'autocorrelation_residual':mp.nstr(err,10),
       'missing_cross_detected':True,
       'certificate':mp.nstr(cert,15),
       'chosen_Rayleigh_II':mp.nstr(mp.re(inn(c,II*c)),15),
       'weight': 'same normalized rank-one W=c c* everywhere'})
out={'status':'PASS_NONINTERVAL_NOT_SPECTRAL_OR_ASYMPTOTIC','mpmath':mp.__version__,
     'decimal_digits':mp.mp.dps,'cases':len(rows),'rows':rows,
     'full_CCM_spectra_computed':False,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'diagnostic_results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
```
<!-- FILE_END: diagnostic_q15.py -->

### `diagnostic_results.json`

<!-- FILE_BEGIN: diagnostic_results.json -->
```json
{
  "status": "PASS_NONINTERVAL_NOT_SPECTRAL_OR_ASYMPTOTIC",
  "mpmath": "1.3.0",
  "decimal_digits": 50,
  "cases": 3,
  "rows": [
    {
      "m": 16,
      "M": 2,
      "U": 2,
      "V": 2,
      "schedule": "FINITE_KERNEL_IDENTITY_DIAGNOSTIC_NOT_LATE_FIXED_SMALL_EPSILON",
      "constraint_residual": "1.879954876e-51",
      "max_reassembly_residual": "1.166298077e-51",
      "autocorrelation_residual": "6.681911775e-51",
      "missing_cross_detected": true,
      "certificate": "2.53102801433806",
      "chosen_Rayleigh_II": "0.031387798620399",
      "weight": "same normalized rank-one W=c c* everywhere"
    },
    {
      "m": 64,
      "M": 3,
      "U": 2,
      "V": 3,
      "schedule": "FINITE_KERNEL_IDENTITY_DIAGNOSTIC_NOT_LATE_FIXED_SMALL_EPSILON",
      "constraint_residual": "1.566570159e-51",
      "max_reassembly_residual": "3.950188244e-51",
      "autocorrelation_residual": "4.677338243e-51",
      "missing_cross_detected": true,
      "certificate": "13.0608055441835",
      "chosen_Rayleigh_II": "-0.164920138996725",
      "weight": "same normalized rank-one W=c c* everywhere"
    },
    {
      "m": 125,
      "M": 4,
      "U": 3,
      "V": 4,
      "schedule": "FINITE_KERNEL_IDENTITY_DIAGNOSTIC_NOT_LATE_FIXED_SMALL_EPSILON",
      "constraint_residual": "1.617399196e-51",
      "max_reassembly_residual": "4.531571904e-51",
      "autocorrelation_residual": "2.67276471e-51",
      "missing_cross_detected": true,
      "certificate": "19.0660839277193",
      "chosen_Rayleigh_II": "-0.0510162406600774",
      "weight": "same normalized rank-one W=c c* everywhere"
    }
  ],
  "full_CCM_spectra_computed": false,
  "script_sha256": "b3d680a213333121599a8a65039818ef5b1b6419f4464729a7e45eec4c83b606"
}
```
<!-- FILE_END: diagnostic_results.json -->

### `source_replay/check.py`

<!-- FILE_BEGIN: source_replay/check.py -->
```python
from pathlib import Path
import json
from collections import Counter
N=128
fac=[Counter() for _ in range(N+1)]
for n in range(2,N+1):
 x=n
 for p in range(2,n+1):
  while x%p==0:fac[n][p]+=1;x//=p
mu=[0]+[(-1)**len(fac[n]) if all(e==1 for e in fac[n].values()) else 0 for n in range(1,N+1)]
lam=[Counter({next(iter(fac[n])):1}) if len(fac[n])==1 else Counter() for n in range(N+1)]
def add(out,v,k=1):
 for p,e in v.items():out[p]+=k*e
cases=0;missing_K=0;missing_II=0
for U in range(1,9):
 for V in range(1,9):
  for n in range(1,N+1):
   I=Counter();J=lam[n] if n<=V else Counter();K=Counter();II=Counter()
   for d in range(1,n+1):
    if n%d:continue
    v=n//d
    if d<=U:
     add(I,fac[v],mu[d])
     for k in range(1,min(V,v)+1):
      if v%k==0:add(K,lam[k],mu[d])
    else:
     for k in range(V+1,v+1):
      if v%k==0:add(II,lam[k],mu[d])
   out=Counter();add(out,I);add(out,J);add(out,K,-1);add(out,II);add(out,lam[n],-1)
   assert all(x==0 for x in out.values()),(n,U,V,out)
   missing_K+=any(K.values());missing_II+=any(II.values());cases+=1
assert missing_K and missing_II
result={'status':'PASS_EXACT_FORMAL_LOG_COEFFICIENTS','cases':cases,'n_max':N,'U_V_range':[1,8],'omitted_K_detected_cases':missing_K,'omitted_II_detected_cases':missing_II,'full_CCM_spectrum_computed':False,'new_arithmetic_exponent':None}
Path(__file__).with_name('results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
```
<!-- FILE_END: source_replay/check.py -->

### `source_replay/results.json`

<!-- FILE_BEGIN: source_replay/results.json -->
```json
{
  "status": "PASS_EXACT_FORMAL_LOG_COEFFICIENTS",
  "cases": 8192,
  "n_max": 128,
  "U_V_range": [
    1,
    8
  ],
  "omitted_K_detected_cases": 3492,
  "omitted_II_detected_cases": 2830,
  "full_CCM_spectrum_computed": false,
  "new_arithmetic_exponent": null
}
```
<!-- FILE_END: source_replay/results.json -->
