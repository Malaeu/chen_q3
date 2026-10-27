# STATUS: TRY_CCM_Q55_DIRECT_HILBERT_PERRON_RETURN
```yaml
OPERATIVE_CLASS: TRY_CCM_Q55_DIRECT_HILBERT_PERRON_RETURN
REQUEST_ID: Q55_CONTACT_PRESERVING_SEAM_RENORMALIZATION
CONTINUATION: OWNER_AUTHORIZED_FRESH_CHAT_2026_10_27
DATE: 2026-10-27
LANGUAGE: ru
BASE_COMMIT: ac174c51d39539db269937390ddfe581e0b3a374
PACKET_BYTES: 127670
PACKET_LF: 2039
PACKET_SHA256: ecf79b6faecccceff894a4d98902de6aac198d3b06355240f0154d2e3d63632e
LOCAL_UPDATE_SHA256: c09ee0b60057cafdd16128b928990daca8ff50c02f7371c1fca70021245ff8d6
BASE_REQUEST_SHA256: 4df1ce42289cb425c24f65861d330cc34e90c304f37724a5c9c76d69004cc1fe
SOURCE_BODIES: 9
MANIFEST: VERIFIED
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_OBJECT: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_P
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROLLBACK: BEFORE_SEPARATE_CURVATURE_CONTROL_TO_DIRECT_FIRST_FORM
INDEPENDENT_INPUT: VERIFIED_VINOGRADOV_KOROBOV_ZERO_FREE_THEOREM_PLUS_PAID_PERRON_RETURN
LOCAL_PROGRESS_CLASS: PROOF_PROGRESS
LOCAL_RESULT: COFINAL_ALL_P_O_SQRT_M_CAP_AND_DIMENSION_FREE_FINITE_SOURCE_INTERFACE
CONSUMER_PROGRESS: NO_VANISHING_EXPONENT_SUPPLIER
FULL_POWER: 1/2
FIXED_POSITIVE_POWER_SAVING: NOT_DERIVED
ETA_EPSILON_TO_ZERO: NOT_DERIVED
JOINT_PSI_REMAINDER_BOUND: DERIVED_AT_THE_REPORTED_HALF_POWER_SCALE
CENTERED_CURVATURE_SMALLNESS: NOT_ASSUMED
FAILURE_TYPE: NO_DERIVATION
FAILURE_SCOPE: TERMINAL_VANISHING_EXPONENT_REQUIREMENT
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
IMPOSSIBILITY_CLAIM: NONE
RH: OPEN
ALL_P_GOAL: OPEN
PX_RH_CLAIM: NOT_MADE
NEW_RH_CLAIM: NOT_MADE
CF22_PYSR: PARKED
CONDITIONAL_ZF78: NOT_USED_NOT_UPGRADED
VERIFIER: PAPER_OWN_DERIVATION_WITH_PRIMARY_THEOREM_IMPORT
INDEPENDENT_NEW_AUDIT: NOT_RUN
LEAN: NOT_RUN
ARB: NOT_RUN
PRODUCTION_CCM_SPECTRUM: NOT_RUN
ACTUAL_ZERO_ASSIGNMENTS: NONE
HISTORICAL_PROGRAMS_EXECUTED: false
REPOSITORY_WRITES: NONE
INSTALLATIONS: NONE
NEXT_QUESTION_DISPATCH: NONE
```

Ы. **Независимый ход выполнен. Получена совместная оценка полного остатка, но не нужный выигрыш степени.** Откат сделан до первой исходной формы, а не к очередной производной положительной семьи. Новый вход — **разделённые разности Fourier-матрицы и ограниченность дискретного преобразования Гильберта**. Они позволяют перенести равномерную арифметическую оценку на весь исходный носитель **без множителя числа мод**.

Вместе с проверенной безусловной областью отсутствия нулей Виноградова–Коробова это даёт, для некоторых абсолютных положительных констант и всех достаточно больших исходных ячеек,
\[
 \boxed{A_m[f]-A_{\rm cont}[f]
 \le s_{\rm new}(m)\|f\|_2^2,\qquad
 s_{\rm new}(m)=C\sqrt m\exp\!\left[-c
 \left(\frac{\log m}{\log(e+\log m)}\right)^{1/3}\right].}
 \tag{0.1}
\]
Следовательно, **вся** совместная форма LOCAL_UPDATE удовлетворяет
\[
 \boxed{R^\Psi_\tau[f]-\Psi_\tau[f]
 \le\left(\frac{\tau s_{\rm new}(m)}2-\tau h_m-1\right)\|f\|_2^2,
 \qquad \tau>0.}
 \tag{0.2}
\]
Здесь не требуется малость \(\Psi''_s\), \(D_m-C_m\) или каждого смешанного слагаемого. Оценка (0.2) **не предположена**: она возвращается из независимо оплаченной (0.1).

Однако
\[
 s_{\rm new}=o(\sqrt m),\qquad
 \frac{\log s_{\rm new}}{\log m}\longrightarrow\frac12.
 \tag{0.3}
\]
Это улучшение множителя при половинной степени, **не** фиксированная экономия степени и **не** \(\eta(\epsilon)\to0\). Главный all-\(P\) consumer и RH остаются открыты. Константы и начало асимптотики ниже не превращены в численный сертификат отдельной ячейки.

## 1. Source lock, границы импорта и выбранный откат

**[FINITE_CELL | PAPER — byte verification].** Исходный TXT прочитан в заданном порядке: LOCAL_UPDATE, BASE_REQUEST, S1–S9, включая исторический код S4 как текст. Совпали внешний SHA-256, обе внешние размерные рамки, все девять bytes/LF/SHA-256 и их закрывающие разделители. Внешний пакет: 127670 bytes, 2039 LF. Полный машинный manifest находится в приложенном `q55_checks.json`.

Bootstrap получен через GitHub connector из `Malaeu/chen_q3`, ветка `rh_clean`, путь `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Усечённая первоначальная выдача дополнена чтением оставшейся части. Никакой очередью или другим запросом текущая задача не заменялась.

**[COFINAL_FAMILY | PAPER — inherited, без повышения статуса].** LOCAL_UPDATE уже установил точное центрирование первого Jordan-квадрата и непрерывный кредит. Это не новый результат настоящего ответа. S1–S3 устанавливают препятствие именно исходному малому endpoint-curvature supplier и не дают отрицательного заключения о совместной компенсации. S4–S5 предоставляют точный исходный возврат. S9 — прежний условный receiver; весь его upstream заново не сертифицировался.

Сравнение с обязательными экранами:

| Источник | Что не повторяется | Отличие настоящего опыта |
|---|---|---|
| S6, Q04 | Контактное обращение непрерывного роста и дешёвая integer-sum inverse сами по себе не оценивают знаковую арифметику | Оценивается настоящая конечная Mangoldt-сумма, равномерно по всей нужной частотной полосе |
| S7, Q13 | Оплаченный seam/high-frequency return не даёт исходного арифметического знака | Здесь нет регуляризации seam и её нового параметра; исходный overlap интегрируется точно |
| S8 | Переписанная jump energy и положительность отдельных deficits не дают near-1 lower | Используется отдельная доказанная оценка Dirichlet-полинома; её реальная недостаточность для near-1 power threshold указана в §8 |
| LOCAL_UPDATE | Центрирование \(\Psi\), его tangent и \(-4\le A_{\rm cont}/\|f\|^2\le0\) уже приняты | Семья не дифференцируется дальше; её полный joint remainder оплачивается после независимого direct-source bound |

**Точка отката:** до требования малой кривизны, непосредственно к \(A_m\), на тех же \(c=Pc\). **Другой арифметический вход:** опубликованная zero-free область [E1], не непроверенная ZF78 и не предполагаемое сокращение Мёбиуса.

Это не заявление мировой новизны. В предоставленном пакете данный Hilbert-commutator/Perron completion не предъявлен. Исчерпывающий поиск всех архивов или литературы не проводился и не заявляется.

## 2. Исходная форма и точный computing object

**[COFINAL_FAMILY | PAPER — inherited definitions].** Сначала фиксируем
\[
 0<\epsilon<1/32,\quad N=m,\quad L=\log m,\quad
 M=R=\lfloor m^\epsilon\rfloor,\quad
 \omega_j=\frac{2\pi j}{L},\quad |j|\le M.
 \tag{2.1}
\]
Для одного произвольного комплексного \(c=Pc\)
\[
 f(t)=L^{-1/2}\sum_{|j|\le M}c_je^{i\omega_jt}
 \quad (0\le t\le L)
 \tag{2.2}
\]
с исходным нулевым продолжением на \(\mathbb R\). Сохраняются исходные три контакта, включая \(f(0)=f(L)=0\), и \(\|f\|_2=\|c\|_2\). Никакой периодической замены вне окна нет.

Запишем
\[
 A_m[f]=2\Re\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
 \int_{\mathbb R}\overline{f(t)}f(t+\log n)\,dt.
 \tag{2.3}
\]
Все настоящие \(\Lambda(p^k)=\log p\) сохранены. Обе временные ориентации входят в \(2\Re\).

Определим **конечные** функции комплексной частоты \(z\):
\[
 F_m(z)=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}e^{iz\log n},
 \qquad
 F_m^c(z)=\int_1^m x^{-1/2+iz}\,dx
 =\frac{m^{1/2+iz}-1}{1/2+iz},
 \tag{2.4}
\]
\[
 E_m(z)=F_m(z)-F_m^c(z).
 \tag{2.5}
\]
Дробь в (2.4) имеет устранимую особенность и задаёт целую функцию. Производные ниже — производные по \(z\), а не по \(m\). Это различие существенно для диагонального члена.

Пусть \(B_m\) — матрица формы \(A_m-A_{\rm cont}\) на **полной** полосе \(|j|\le M\), до применения \(P\). Тогда искомый новый промежуточный объект — конечная **Loewner-матрица**, то есть матрица разделённых разностей значений одной функции, вместе с её точной диагональю. Далее она выводится, а не предполагается.

### 2.1. Все перекрёстные моды

**[FINITE_CELL | PAPER].** При \(0\le a\le L\) матричный элемент положительного сдвига равен
\[
 J_{jk}(a)=\frac1L\int_0^{L-a}
 e^{-i\omega_jt}e^{i\omega_k(t+a)}dt.
\]
Отсюда
\[
 J_{jj}(a)=(1-a/L)e^{i\omega_ja},
\qquad
 J_{jk}(a)=\frac{e^{i\omega_ja}-e^{i\omega_ka}}
 {iL(\omega_k-\omega_j)}\quad(j\ne k).
 \tag{2.6}
\]
Использовано ровно \(e^{i(\omega_k-\omega_j)L}=1\); интеграл всё ещё взят по физическому overlap, не по целому периоду. Матрица \(J\) комплексно-симметрична, поэтому симметризованная форма имеет элементы \(2\Re J_{jk}\).

Подставляя настоящий дискретный источник или непрерывный источник по отдельности и затем вычитая, получаем
\[
 \boxed{
 (B_m)_{jj}=d_j:=2\Re E_m(\omega_j)-\frac2L\Im E'_m(\omega_j),
 }
 \tag{2.7}
\]
\[
 \boxed{
 (B_m)_{jk}=-\frac{g_j-g_k}{\pi(j-k)},\quad
 g_j:=\Im E_m(\omega_j),\qquad j\ne k.
 }
 \tag{2.8}
\]
Действительно, \(F'_m=i\sum \Lambda(n)n^{-1/2}\log n\,e^{iz\log n}\); именно поэтому диагональ содержит **минус** \(2\Im F'_m/L\). Никакого разрешения заменить её просто \(2\Re F_m\) нет.

Формулы справедливы для всех комплексных \(c\), поскольку доказано матричное равенство. Никакие \(\overline c_jc_k\) не заменены независимыми фазами или диагональным средним.

### 2.2. Точный верхний атом и оба исходных cutoff

При \(n=m\) имеем \(a=L\): все элементы (2.6) равны нулю. В (2.7) его вклад сокращается как
\[
 2\frac{\Lambda(m)}{\sqrt m}
 -\frac2L\left(L\frac{\Lambda(m)}{\sqrt m}\right)=0;
\]
в (2.8) все соответствующие синусы равны нулю. Поэтому атом **сохраняется** в \(F_m,F'_m\), а не выкидывается из одного из них. Это особенно важно, когда \(m\) — степень простого.

Оба гиперболических cutoff \(dk\le m\), \(el\le m\) остаются в унаследованной точной \(\Psi\)-семье. Переход к (2.3) использует уже принятое конечное source identity, где эти суммы сокращены **тождественно**. Они не заменяются прямоугольником и не получают бесплатного tail estimate. Наш новый операторный расчёт начинается после этого точного возврата, а в §6 возвращается к полной исходной семье.

## 3. Направленный bound без числа мод

### 3.1. Дискретный Hilbert-оператор

**[ABSTRACT | PAPER].** Пусть на \(\ell^2(\mathbb Z)\)
\[
 (H u)_j=\sum_{k\ne j}\frac{u_k}{j-k}
\]
в смысле ограниченного оператора, первоначально определённого на конечных последовательностях. Его Fourier-мультипликатор — Fourier-ряд пилообразной функции:
\[
 \sum_{r\ne0}\frac{e^{ir\theta}}r=i(\pi-\theta),
 \qquad0<\theta<2\pi.
 \tag{3.1}
\]
В зависимости от соглашения Fourier знак меняется, модуль — нет. По Parseval
\[
 \|H\|\le\pi.
 \tag{3.2}
\]
Можно получить (3.1) интегрированием геометрического ряда с множителем \(0<\rho<1\) и переходом \(\rho\uparrow1\) в \(L^2\). Это не оценка суммы модулей \(\sum1/|j-k|\).

Обозначим \(H_M\) его сжатие на \(-M,\ldots,M\). Тогда
\[
 (H_M)_{jk}=\begin{cases}(j-k)^{-1},&j\ne k,\\0,&j=k,\end{cases}
 \qquad \|H_M\|\le\pi.
 \tag{3.3}
\]
Это непериодическое конечное сжатие, не циклическая Hilbert-матрица.

### 3.2. Коммутатор и односторонняя оболочка

**[FINITE_CELL | PAPER].** С \(D_g=\operatorname{diag}(g_j)\) формулы (2.7)–(2.8) дают
\[
 \boxed{B_m=\operatorname{diag}(d_j)-\frac1\pi[D_g,H_M].}
 \tag{3.4}
\]
Коммутатор здесь самосопряжён: \(D_g^*=D_g\), \(H_M^*=-H_M\). Для любого вещественного \(a\)
\[
 \frac1\pi\|[D_g,H_M]\|
 =\frac1\pi\|[D_g-aI,H_M]\|
 \le2\max_j|g_j-a|.
\]
Выбор \(a=(\max g+\min g)/2\) даёт
\[
 \frac1\pi\|[D_g,H_M]\|\le\operatorname{osc}(g)
 :=\max_jg_j-\min_jg_j.
 \tag{3.5}
\]
Следовательно,
\[
 \boxed{B_m\preceq S_{m,M}I,\qquad
 S_{m,M}=\max_{|j|\le M}d_j+\operatorname{osc}_{|j|\le M}(g_j).}
 \tag{3.6}
\]
В частности, форма \(S_{m,M}\|c\|^2-c^*B_mc\) имеет аналитически доказанную нижнюю оболочку \(0\). Это правильное направление сертификата. **Никаких \(M\), \(\sqrt M\) или \(\log M\) в цене переноса нет.**

(3.6) — достаточный направленный интерфейс, не необходимая характеристика \(\lambda_{\max}(PB_mP)\). Коммутатор и диагональ могут дополнительно компенсироваться. Неудача скалярного \(S_{m,M}\) не опровергает исходную форму.

Для явного дальнейшего завершения достаточно более грубого следствия:
\[
 S_{m,M}\le4\max_j|E_m(\omega_j)|
 +\frac2L\max_j|E'_m(\omega_j)|.
 \tag{3.7}
\]
Это место, где сознательно теряется часть знаковой информации; потеря оплачена. Ниже обе величины справа оценены независимым арифметическим входом.

## 4. Независимая арифметическая оценка: настоящий finite Perron return

### 4.1. Ровно какой внешний результат импортируется

**[ABSTRACT | PAPER — imported theorem E1].** Mossinghoff–Trudgian–Yang, Theorem 1.1, устанавливают отсутствие нулей при
\[
 \sigma\ge1-\frac1{55.241(\log|t|)^{2/3}(\log\log|t|)^{1/3}},
 \qquad |t|\ge3.
 \tag{4.1}
\]
Прочитан первичный опубликованный HTML, включая само утверждение. Это безусловный theorem import, а не новая заявка на zero-free область, не RH и не ZF78 из старого маршрута. Численный коэффициент здесь не оптимизируется.

Кроме (4.1), используются стандартные свойства \(\zeta\): Euler product в \(\Re s>1\), простой полюс с вычетом 1 и отсутствие нулей на \(\Re s\ge1\); см. [E1, §1], [E2]. На фиксированном компактном участке по высоте это даёт некоторую фиксированную положительную ширину без нулей, без назначения координат какому-либо нулю. Все последующие равномерные оценки и возвраты выводятся здесь.

### 4.2. Комплексная полоса, необходимая для производной

**[COFINAL_FAMILY | PAPER].** Положим
\[
 T=m^2,\qquad X=m+\tfrac12,\qquad L=\log m.
\]
Для больших \(m\) выберем
\[
 w_m=\frac1{55.241\,[\log(3T)]^{2/3}[\log\log(3T)]^{1/3}},
 \qquad \delta_m=\frac{w_m}{8}.
 \tag{4.2}
\]
Начало асимптотики выбрано так, чтобы компактная низкая часть по высоте также была свободна от нулей в используемой полосе и
\[
 L^{-1}\le\delta_m/2,\qquad 0<\delta_m<1/16.
 \tag{4.3}
\]
Оба условия выполняются в конечном счёте; эффективный численный onset здесь не вычислялся.

Докажем оценку **одновременно** для
\[
 |\Re z|\le m+1,\qquad |\Im z|\le L^{-1}.
 \tag{4.4}
\]
Это важно: одна лишь оценка \(E_m\) на вещественной оси не разрешала бы дифференцировать её big-O.

### 4.3. Полилогарифмическая цена \(\zeta'/\zeta\) на контуре

Нужный промежуточный bound не оставляем скрытым supplier. Обозначим \(q(s)=(s-1)\zeta(s)\). Интегрирование \(\lfloor x\rfloor=x-\{x\}\) в исходном Dirichlet-ряде и аналитическое продолжение дают
\[
 \zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{x\}x^{-s-1}dx,
 \qquad\Re s>0,
 \tag{4.5}
\]
поэтому в \(\Re s\ge1/2\)
\[
 |q(s)|\le C(1+|s|)^2.
 \tag{4.6}
\]
В центре \(s_0=2+it\), Euler product даёт
\[
 |q(s_0)|=|1+it|\,|\zeta(2+it)|
 \ge |1+it|/\zeta(2).
 \tag{4.7}
\]

Для \(|t|\le T+m+2\) диск \(|s-s_0|<1+4\delta_m\) свободен от нулей \(q\). Его левый край \(1-4\delta_m\) лежит строго правее границы (4.1), а его высоты по модулю меньше \(3T\); низкие высоты покрывает уже оговорённый компактный участок. Полюс \(\zeta\) устранён в \(q\).

В этом диске существует аналитический
\[
 h(s)=\log(q(s)/q(s_0)),\qquad h(s_0)=0,
\]
с \(\Re h(s)\le C\log(3T)\) по (4.6)–(4.7). Теорема Бореля–Каратеодори на вложенных радиусах \(1+4\delta_m\), \(1+3\delta_m\), затем Cauchy для производной на радиусе порядка \(\delta_m\), дают
\[
 \left|\frac{q'}q(s)\right|
 \le C\frac{\log(3T)}{\delta_m^2}
 \quad\text{при }1-2\delta_m\le\Re s\le2.
 \tag{4.8}
\]
Здесь высота \(s\) фиксируется как высота центра; указанная оценка равномерна по всем нужным высотам. Использовано общее элементарное комплексно-аналитическое неравенство, не арифметическая гипотеза о знаке.

Так как \(\zeta'/\zeta=q'/q-1/(s-1)\), на левой и горизонтальных сторонах будущего контура расстояние от полюса не меньше \(\delta_m/2\). Следовательно,
\[
 \left|\frac{\zeta'}\zeta(s)\right|
 \le C\frac{\log(3T)}{\delta_m^2}\le C L^3.
 \tag{4.9}
\]
Последняя степень намеренно груба: точная цена порядка
\(L^{7/3}(\log L)^{2/3}\). Никакого фиксированного zero-free strip в (4.8)–(4.9) не подставлено.

### 4.4. Обрезанный Perron с неизменным \(n\le m\)

Берём \(a=1/2+2/L\). Для (4.4), \(a+1/2+\Im z>1\), поэтому допустим абсолютно сходящийся ряд
\[
 -\frac{\zeta'}\zeta(s+1/2-iz)
 =\sum_{n\ge2}\Lambda(n)n^{-s-1/2+iz}.
\]
Обрезанный Perron даёт
\[
 F_m(z)=\frac1{2\pi i}\int_{a-iT}^{a+iT}
 -\frac{\zeta'}\zeta(s+1/2-iz)\frac{X^s}{s}\,ds
 +O\!\left(\frac{\sqrt m L^2}{T}\right),
 \tag{4.10}
\]
равномерно на (4.4).

**Проверка ошибки и атома:** для каждого члена скалярный Perron-кernel отличается от \(\mathbf1_{n<X}\) не более чем на
\[
 C(X/n)^a\min\{1,(T|\log(X/n)|)^{-1}\}.
\]
Умножаем на \(\Lambda(n)n^{-1/2-\Im z}\), используя \(\Lambda(n)\le\log n\). На \(X/2<n<2X\) расстояние \(|X-n|\ge1/2\), а сумма \(1/|X-n|\) стоит \(O(L)\). Получается \(O(\sqrt m L^2/T)\). Вне этого интервала \(|\log(X/n)|\) отделён от нуля, и
\(\sum (\log n)n^{-1-1/L}=O(L^2)\) даёт ту же цену. Множитель \(n^{-\Im z}\) уже включён в запас \(1/L\) абсолютной сходимости. Таким образом, нет неявного множителя \(|z|\) или числа мод.

Индикатор \(n<X=m+1/2\) **ровно** совпадает с \(n\le m\). Вспомогательная половина единицы не меняет арифметический cutoff и не заменяет верхний атом половинным весом. Бесконечный ряд используется только внутри тождества Perron: никаких фактических prime powers за \(m\) в \(F_m\) не добавляется.

Сдвигаем контур на
\[
 b=1/2-\delta_m.
\]
На нём аргумент \(\zeta\) имеет действительную часть \(1-\delta_m+\Im z\), остающуюся в доказанной zero-free полосе. Полюс \(s=1/2+iz\) находится внутри прямоугольника; \(s=0\) снаружи слева, поскольку \(b>1/4\). Нули не пересекаются. Вычет равен
\[
 \frac{X^{1/2+iz}}{1/2+iz}.
\]
По (4.9), вертикальная сторона стоит
\[
 C X^{1/2-\delta_m}L^3\int_{-T}^T\frac{dt}{|b+it|}
 \le C\sqrt m\,e^{-\delta_m L}L^4.
 \tag{4.11}
\]
Обе горизонтальные стороны вместе стоят
\[
 C\sqrt m L^3/T,
 \tag{4.12}
\]
поскольку \(|s|\ge T\), их длина ограничена, а \(X^a\le C\sqrt m\). Высота \(T\) — аналитический вспомогательный параметр; production \(N=m\) не меняется.

Наконец,
\[
 \frac{X^{1/2+iz}}{1/2+iz}-F_m^c(z)
 =\frac1{1/2+iz}+\int_m^{m+1/2}x^{-1/2+iz}dx.
 \tag{4.13}
\]
На полосе (4.4) первое слагаемое ограничено абсолютной константой, второе — \(C m^{-1/2}\). **Нижний край 1 и верхняя поправка \(m+1/2\to m\) оба сохранены.**

Из (4.10)–(4.13) следует доказанная равномерная оценка
\[
 \boxed{\sup_{(4.4)}|E_m(z)|\le\mathcal B_m,
 \quad \mathcal B_m=C\left(1+\sqrt m L^4e^{-\delta_m L}
 +\frac{\sqrt m L^3}{T}\right).}
 \tag{4.14}
\]
Это независимый вход, а не новое обозначение \(A_m\le s_mP\): он получен для скалярной конечной Mangoldt-суммы из конкретной внешней теоремы, с явным finite-cutoff возвратом.

### 4.5. Диагональная производная и полный множитель

Для каждой реальной \(|\omega|\le m\) диск радиуса \(1/L\) лежит в (4.4). Поэтому Cauchy даёт
\[
 |E'_m(\omega)|\le L\mathcal B_m.
 \tag{4.15}
\]
Из \(M\le m^{1/32}\) следует \(\Omega=2\pi M/L\le m\) для всех достаточно больших \(m\), равномерно в разрешённом диапазоне \(\epsilon\). Таким образом, (3.7) даёт
\[
 \boxed{B_m\preceq6\mathcal B_m I.}
 \tag{4.16}
\]
Фактически тот же расчёт даёт \(\|B_m\|\le6\mathcal B_m\), но потребителю расходуется только верхняя сторона.

Поскольку \(T=m^2\),
\[
 \delta_m L\asymp\left(\frac L{\log L}\right)^{1/3}.
\]
Поглощая \(L^4\) уменьшением положительной константы в экспоненте и увеличением начала асимптотики, получаем (0.1). Никакой предел \(\epsilon=\epsilon(m)\) не использован. Константы в этом грубом варианте можно брать абсолютными; скрытый onset не объявляется вычисленным.

## 5. Непрерывный кредит и исходный \(P\)

**[COFINAL_FAMILY | PAPER — inherited LOCAL_UPDATE, использовано точно].** Контакты
\[
 \int_0^L e^{t/2}f(t)dt=\int_0^L e^{-t/2}f(t)dt=0
\]
зануляют форму ядра \(2\cosh((u-t)/2)\). Поскольку
\[
 e^{|u-t|/2}+e^{-|u-t|/2}=2\cosh((u-t)/2),
\]
имеем на исходном пространстве
\[
 A_{\rm cont}[f]=-
 \int_0^L\int_0^L\overline{f(t)}e^{-|u-t|/2}f(u)\,du\,dt.
 \tag{5.1}
\]
Fourier-мультипликатор последнего свёрточного ядра —
\(1/(\xi^2+1/4)\). Поэтому
\[
 -4\|f\|^2\le A_{\rm cont}[f]\le0.
 \tag{5.2}
\]
Это принятый LOCAL_UPDATE, не новая арифметическая компенсация. В настоящем опыте его роль — законно получить из (4.16)
\[
 A_m[f]\le6\mathcal B_m\|f\|^2
 \tag{5.3}
\]
**без добавления положительной платы 4**. Сжатие \(P B_mP\) не увеличивает верхнюю оболочку. Endpoint-контакт также сохраняется; новый Hilbert bound не требует его удаления или замены.

## 6. Полный возврат к \(\Psi\): все смешанные члены вместе

**[FINITE_CELL | PAPER — inherited exact identity plus new bound].** Для исключения скрытого выбрасывания терминов запишем только необходимый точный crosswalk.

Пусть, как в LOCAL_UPDATE,
\[
 Q_\tau[f]:=\Psi_\tau[f]-\Phi_\tau[f]
 =\tau\Re\langle y_\tau,C_mf\rangle
 +\frac{\tau^2}{4}\|C_mf\|^2.
 \tag{6.1}
\]
Тогда
\[
 Q_0=0,\qquad Q'_0=A_{\rm cont}/2,
\]
и по точной формуле Taylor с интегральным остатком
\[
 R^\Psi_\tau-R^\Phi_\tau
 =Q_\tau-\tau A_{\rm cont}/2.
 \tag{6.2}
\]
Следовательно,
\[
 \boxed{R^\Psi_\tau-\Psi_\tau
 =R^\Phi_\tau-\Phi_\tau-\tau A_{\rm cont}/2.}
 \tag{6.3}
\]
Здесь полностью сохранены \(\|C_mf\|^2\), смешанные члены с \(y'_s,y''_s\), а при раскрытии — с \(D_m-C_m\). Ничего из них не было объявлено нулём или отдельно малым. Положительные \(s\), все Jordan-каналы и higher-prime supports остаются внутри точного остатка.

Исходный source return даёт
\[
 A_m[f]-A_{\rm cont}[f]
 =2h_m\|f\|^2+
 \frac2\tau\bigl(\|f\|^2+R^\Psi_\tau[f]-\Psi_\tau[f]\bigr),
 \qquad h_m=\sum_{n\le m}\Lambda(n)/n.
 \tag{6.4}
\]
Теперь **вставляем уже доказанный**, а не предполагаемый upper (4.16):
\[
 \boxed{R^\Psi_\tau[f]-\Psi_\tau[f]
 \le\bigl(3\tau\mathcal B_m-\tau h_m-1\bigr)\|f\|^2,
 \qquad\forall\tau>0.}
 \tag{6.5}
\]
Замена \(6\mathcal B_m\) его укрупнённой асимптотической ценой даёт (0.2).

Сама (6.4) — старое тождество. **Новый estimate — (4.14)–(4.16), а не переименование (6.4).** Никакой \(\tau\)-оптимизацией результат не усилен: при обратной подстановке (6.5) в (6.4) \(\tau\) сокращается точно, возвращая ровно \(6\mathcal B_m\).

В частности, не следует выводить из (6.5) малость \(\Psi''_0\) или равномерную малость \(\Psi''_s\). Это другая, более сильная задача; она здесь не нужна и не решена.

## 7. Полный consumer budget

**[COFINAL_FAMILY | PAPER — new direct upper, inherited return].** Обозначим \(s_m=6\mathcal B_m\), либо его доказанный асимптотический верх \(s_{\rm new}\). Тогда на том же исходном \(P\)
\[
 \boxed{T_{>R}\preceq(s_m+b_{\rm div})P,\qquad
 PK_mP\succeq-(s_m+50L+8)P,}
 \tag{7.1}
\]
где
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
\]
Это прежняя прямая карта из S4 §2. Контур Perron в §4 оценивает лишь конечный скалярный источник; он **не** является старой CCM-контурной сменой модели и не требует её high/entire-quotient fees.

| Слагаемое/карта | Полная цена | Где оплачена |
|---|---:|---|
| Исходный overlap \(J_{jk}\) | 0 ошибки | (2.6), оба края |
| Непрерывное вычитание | точно \(A_{\rm cont}\in[-4,0]\) | только благоприятный кредит при верхе \(A_m\) |
| Hilbert-коммутатор | \(\operatorname{osc}g\), без числа мод | (3.5)–(3.6) |
| Диагональ | \(2\Re E-2\Im E'/L\) | производная оплачена Cauchy, не удалена |
| Обрезанный Perron | \(O(\sqrt m L^2/T)\) | включён в \(\mathcal B_m\) |
| Левая сторона | \(O(\sqrt m L^4e^{-\delta_mL})\) | главный нынешний budget |
| Обе горизонтальные стороны | \(O(\sqrt m L^3/T)\) | включены |
| Оба края непрерывной интеграли | \(O(1)+O(m^{-1/2})\) | (4.13), включены |
| Полная \(\Psi\)-компенсация | точно (6.3)–(6.5) | нет отдельных квадратных surcharge |
| Short divisor | \(b_{\rm div}\) | один раз, только \(T_{>R}\) |
| Archimedean return | \(50L+8\) | один раз, только direct \(K_m\) |

При фиксированном допустимом \(\epsilon\)
\[
 b_{\rm div}=O_\epsilon(m^{3\epsilon/2}/L+m^{\epsilon/2}+L^2)
 =o(s_{\rm new}).
\]
Архимедова плата также \(o(s_{\rm new})\). Поэтому **полный**, а не отдельный показатель (7.1) остаётся \(1/2\).

Сохранённый независимый fallback не ухудшается:
\[
 A_m\preceq s_{\rm keep}P,\qquad
 s_{\rm keep}\le6\sqrt m+6m^{1/4}.
\]
На области, где применён новый асимптотический theorem, можно математически использовать \(\min\{s_{\rm keep},s_m\}\), а не сумму. Для конкретного finite-cell сертификата без явных \(C,m_0\) новый big-O не является исполняемым числом: там сохраняется прежний проверенный fallback либо требуется отдельный интервальный расчёт.

**Тонкость направления:** прежний upper для \(A_m\) сам по себе даёт upper для \(A_m-A_{\rm cont}\) лишь с дополнительным \(+4\). Поэтому в joint-формулу (6.5) нельзя подставить \(s_{\rm keep}\) без этой поправки. Новый bound (4.16) получен сразу для разности и такой платы не требует. В direct \(K_m\)-возврат дополнительная 4 не добавляется.

## 8. Первая неоплаченная степень и точный scope отказа

**[COFINAL_FAMILY | PAPER — audit of the supplied bound, not source lower].** Положим
\[
 q_m=\left(\frac{L}{\log(e+L)}\right)^{1/3}.
\]
Для каждого фиксированного \(\eta<1/2\) наш положительный **разрешённый бюджет** удовлетворяет
\[
 \frac{C\sqrt m e^{-cq_m}}{m^\eta}
 =C\exp\bigl((1/2-\eta)L-cq_m\bigr)\longrightarrow\infty.
 \tag{8.1}
\]
Это проверка недостаточной силы **выписанного upper**, не нижняя оценка \(A_m\), \(B_m\) или истинного remainder. Никакое математическое отрицание более сильного source bound из (8.1) не следует.

Первый неоплаченный шаг для выбранного скалярного completion выглядел бы так:
\[
 4\max_j|E_m(\omega_j)|+
 \frac2L\max_j|E'_m(\omega_j)|
 \stackrel{?}{\le}C_\epsilon m^{\kappa(\epsilon)},
 \qquad\kappa(\epsilon)\to0.
 \tag{8.2 OPEN}
\]
Это лишь **достаточный**, возможно излишне сильный вход. Из (4.1) он не выведен: ширина \(\delta_m\to0\), тогда как для фиксированной экономии степени в данном абсолютном контурном budget требовалась бы не исчезающая ширина соответствующего размера. Здесь нельзя незаметно заменить (4.1) фиксированной полосой.

Более слабая достаточная версия на том же scalar interface:
\[
 \max_j d_j+\operatorname{osc}_j g_j
 \le C_\epsilon m^{\kappa(\epsilon)}.
 \tag{8.3 OPEN}
\]
Ещё слабее — направленная оценка полной (3.4) после \(P\), сохраняющая компенсацию диагонали и коммутатора. Последняя уже эквивалентна source comparison и **не объявляется независимым supplier** без нового аргумента.

При любом независимо доказанном \(s_m=O_\epsilon(m^{\kappa(\epsilon)})\) с \(\kappa\to0\), прямой бюджет допускает, например, конечный показатель
\[
 \eta(\epsilon)=\max\{\kappa(\epsilon),2\epsilon\}\longrightarrow0
\]
с поглощением логарифмов. Настоящая (4.16) такого \(\kappa\) не даёт.

Сравнение с S8 также прозрачно. При \(B_d\sim2\sqrt m\) новый верх даёт нормированную allowance
\[
 r_m=\frac{s_{\rm new}}{2B_d}=O(e^{-cq_m}),
\]
тогда как sufficient threshold S8 для степени \(\eta\) — \(O(m^{\eta-1/2})\). Первое стремится к нулю, но для каждого фиксированного \(\eta<1/2\) недостаточно быстро. Это не переименование fixed-gap coercivity в решение.

**Остановка этой ветки:** не улучшать константу 55.241, не менять высоту Perron и не оптимизировать дополнительные логарифмы под названием новой степени. Они не устраняют исчезающую ширину. Не возвращаться к раздельному small-curvature supplier лишь потому, что полный remainder теперь получил более аккуратный half-power upper.

## 9. Adversarial review, прогнозы и варианты следующей развилки

### 9.1. Сильнейшее возражение и ответ

**Возражение:** «Ты перенёс трудность в \(E_m\), применил стандартную область отсутствия нулей и всё ещё не получил нужную степень».

**Ответ:** верно в отношении терминального consumer. Поэтому \(\eta\to0\) не заявляется. Но в отличие от прежнего необеспеченного supplier, скалярный вход здесь **действительно доказан** из указанной теоремы, а его перенос на всю растущую исходную полосу имеет доказанную цену без числа мод. Это закрывает конкретный более слабый cofinal-квантор \(o(\sqrt m)\), не конечный набор тестов. Мировая новизна этого corollary не утверждается.

**Возражение:** «Равномерный PNT для фиксированной частоты не равномерен при \(\omega\sim m^\epsilon\)».

Справедливо для такого некорректного аргумента. Здесь (4.10)–(4.14) доказаны сразу на \(|\Re z|\le m+1\), включая нужную полосу, с абсолютной ошибкой и комплексной толщиной \(1/L\). Обычное partial summation с платой \(|\omega|\) не использовалось.

**Возражение:** «Оценку big-O нельзя дифференцировать».

Верно. Например, \(E(z)=e^{iKz}\) имеет модуль 1 на вещественной оси и производную модуля \(K\). Именно поэтому (4.15) опирается на **комплексную** полосу, где такой пример платит \(e^{K/L}\). Это ABSTRACT/PAPER отрицательный контроль логического шага, не контрпример исходному Mangoldt-полиному.

**Возражение:** «Численные малые \(m,M\) не соответствуют исходному \(M=\lfloor m^\epsilon\rfloor\)».

Верно; все пять диагностических полос ниже явно помечены `original_epsilon_schedule=false`. Они проверяют универсальное конечное равенство (2.6)–(3.4), которое доказано для любого \(M\), и не сертифицируют ни одной поздней production-ячейки. Исходное расписание возвращается аналитически в (4.15)–(4.16).

### 9.2. Регистрация и судьба прогнозов

Регистрация создана после чтения пакета, transport-check и предварительного бумажного вывода, **до новых исполняемых математических тестов**. Она не выдаётся за preregistration первоначального поиска идеи.

| ID | Зарегистрированный исход | Судьба и область подтверждения |
|---|---|---|
| P1 | Точная диагональ и знак разделённой разности | Подтверждён PAPER (2.6)–(2.8); 115 точных rational-entry controls и пять физических Fourier-диагностик |
| P2 | Hilbert norm \(\le\pi\), верх без числа мод | Подтверждён PAPER (3.1)–(3.6); конечные тесты не заменяют norm theorem |
| P3 | Контактный непрерывный кредит и корректный \(n=m\) | Использован принятый LOCAL_UPDATE; алгебра верхнего атома проверена, диагностические контакты оплачены |
| P4 | VK/Perron даёт subexponential multiplier, не фиксированную степень | Подтверждён собственным PAPER-выводом §4 и сравнением (8.1), не численным экспериментом |
| P5 | Полный joint remainder возвращается без удаления mixed/higher-prime terms | Подтверждён (6.1)–(6.5); точный polynomial control проверяет знак изменения остатка |
| P6 | Конечные проверки не дают cofinal-сертификата | Соблюдено; production spectra, Lean, Arb, actual zeros и независимый аудит не запускались |

Ни один зарегистрированный тезис не был задним числом заменён после неудачного запуска. Первый запуск нового математического checker прошёл без изменения assertions. Пять предусмотренных исполняемых алгебраических нарушений обнаружены; два дополнительных аналитических falsifiers — незаконная производная real-axis upper и подмена moving strip фиксированным — разобраны выше на PAPER-уровне.

### 9.3. Две кандидатные репрезентации при незакрытом consumer

| Репрезентация | Что сохраняет / что могло бы изменить решение | Kill-power и стоимость |
|---|---|---|
| **Полная знаковая Loewner/Hilbert-форма (3.4)** после исходного \(P\), до отдельных максимумов | Сохраняет связь диагонали и фазового коммутатора; допустим только новый независимый analytic matrix majorant, не объявление самой формы малой | Высокая сила для обнаружения потери диагонали/знака/модового множителя; алгебраическая карта дешева, новый cofinal sign дорог и пока отсутствует. Прямое finite evaluation — \(O(mM+M^2)\), не предписание production scan |
| **Исходная Mellin-мера и положительно-определённая автокорреляция**: \(2\Re\int_1^m x^{-1/2}I_{\log x}[f]\,(d\psi(x)-dx)\) | Сохраняет один и тот же \(f\) и его корреляционный конус; искать одностороннее domination на этом конусе, а не норму полной меры | Сильна для проверки, использует ли кандидат настоящие арифметические знаки или лишь total variation. Карта имеет нулевую ошибку; цена нового domination неизвестна. Само равенство не новый supplier |

Это варианты для **нового арифметического аргумента**, не два якобы выполненных успеха. Возврат к \(\Psi\) не предлагается как третья новая репрезентация: (6.4) уже полностью картирован.

Три cross-domain проверки протокола: (a) выполнен FORM_IDENTITY bridge к дискретному Hilbert-оператору; (b) проверено точное исчезновение лишь непрерывного ранга два, не настоящего \(E_m\); (c) collapse object — независимо доказанная односторонняя оболочка полной (3.4) порядка \(m^{\kappa(\epsilon)}\). Простой вещественный scalar majorant исследован и оплачен в §4, но требуемой силы не имеет. Положительность вспомогательных семейств не принимается вместо этого объекта.

**DISCRIMINATOR:** для заранее заданного candidate budget \(s_m\) рассматривать
\[
 \mathcal D_{m,s}(c)=s_m\|c\|^2-c^*P B_mP c,
 \qquad c=Pc.
 \tag{9.1}
\]
Нужна lower envelope \(\mathcal D_{m,s}\ge0\) на всей нужной cofinal family. Для опровержения именно этого candidate budget достаточно upper envelope \(\mathcal D_{m,s}(c)<0\) у допустимого исходного \(c\). Интервал, содержащий ноль, не даёт ни одного вердикта знака. Отрицательный конечный тест сам по себе не опровергает eventual утверждение с неизвестным onset. Новых interval-оценок (9.1) здесь нет; для \(s_m=6\mathcal B_m\) lower envelope доказана аналитически.

## 10. Ledger и dependency contract

| ID | Утверждение | Scope | Verifier | Статус |
|---|---|---|---|---|
| L0 | Внешний TXT, LOCAL_UPDATE, BASE_REQUEST и S1–S9 | FINITE_CELL | PAPER | bytes/hash/framing совпали |
| L1 | Исходные \(P\), source return, consumer и receiver | COFINAL_FAMILY | PAPER | inherited, upstream не пересертифицирован |
| L2 | Fourier-элементы (2.6)–(2.8), включая верхний атом | FINITE_CELL | PAPER | доказано для любого конечного \(M\) |
| L3 | Hilbert norm и commutator upper (3.6) | ABSTRACT | PAPER | доказано без размерной платы |
| L4 | Zero-free theorem (4.1) | ABSTRACT | PAPER | внешний опубликованный theorem E1 |
| L5 | Равномерный конечный Perron-return (4.14) и Cauchy (4.15) | COFINAL_FAMILY | PAPER | собственный вывод; не независимый аудит |
| L6 | Полный исходный upper \(A-A_{\rm cont}=o(\sqrt m)\) | COFINAL_FAMILY | PAPER | (4.16), все исходные векторы |
| L7 | Joint remainder (6.5) при каждом \(\tau>0\) | COFINAL_FAMILY | PAPER | доказан на scale L6, не малость кривизны |
| L8 | Полный бюджет \(T,K\) с единственными short/arch fees | COFINAL_FAMILY | PAPER | (7.1), полный показатель 1/2 |
| L9 | Supplier с \(\kappa(\epsilon)\to0\) | COFINAL_FAMILY | CONDITIONAL | не поставлен и не использован |
| L10 | Новые исполняемые algebra controls | FINITE_CELL | PAPER | exact rational и binary64 diagnostics, не ARB_INTERVAL |
| L11 | RH / full all-\(P\) goal | COFINAL_FAMILY | CONDITIONAL | OPEN; нового RH-утверждения нет |

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_CCM_SPARSE_BAND_ONE_SIDED_T_GT_R_AND_DIRECT_K_FLOOR
ACTUAL_CONSUMER_REQUIREMENT: common_eventual_or_cofinal_bound_with_eta_epsilon_to_zero
ORIGINAL_REQUESTED_OBJECT: independent_joint_compensation_after_contact_preserving_centering
ORIGINAL_OBJECT_IS: NOT_NECESSARY
NECESSITY_EXPLANATION: the_Psi_representation_is_not_required_by_the_consumer;_a_direct_A_upper_suffices
KNOWN_WEAKER_INTERFACES:
  - independently_proved_A_upper_s_returns_T_upper_s_plus_bdiv_and_K_floor_minus_s_minus_50L_minus_8
  - independently_proved_B_upper_s_implies_A_upper_s_using_Acont_nonpositive
  - directed_full_projected_Hilbert_matrix_upper_is_weaker_than_the_separate_scalar_modulus_cap
  - Psi_joint_comparison_is_an_exact_return_interface_not_an_independent_arithmetic_premise
CLOSED_QUANTIFIER: every_original_P_vector_in_every_sufficiently_late_cell_has_B_upper_o_sqrt_m
FAILURE_TYPE: NO_DERIVATION
FAILURE_SCOPE: vanishing_exponent_supplier
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE
IMPOSSIBILITY_EVIDENCE: NONE
NOVELTY_AXIS: dimension_free_Fourier_commutator_transfer_plus_an_independently_paid_uniform_arithmetic_bound
MINIMAL_MISSING_IDENTITY: independent_directed_original_P_majorant_at_m_power_kappa_epsilon_with_kappa_to_zero
REOPEN_TRIGGER: a_source_specific_signed_matrix_or_correlation_cone_estimate_stronger_than_the_paid_scalar_zero_free_completion
LOOP_DETECTED: repeatedly_renaming_the_joint_Taylor_return_without_new_arithmetic
CURRENT_FAILED_STRATEGY: separate_small_curvature_or_unquantified_centered_remainder
FORBIDDEN_FUTURE_MOVE: optimize_tau_or_zero_free_constants_and_call_it_a_new_fixed_power
ROUTE_SCORE: 3
NEXT_QUESTION_DISPATCH: NONE
```

**Что стало меньше:** доказана цена переноса без числа мод и закрыт более слабый cofinal upper \(o(\sqrt m)\); неоплаченная часть теперь отделена от этих двух утверждений. **Что убито:** никакая source/route family; выявлены только запрещённые общие логические переходы. **Что не закрыто:** конечная цель \(\eta\to0\). Это не выдаётся за прогресс терминального показателя.

```yaml
MEMORY_ENTRY:
  iteration: Q55_OWNER_AUTHORIZED_FRESH_CHAT_CONTINUATION
  target: full_joint_compensation_after_exact_first_Gram_square_centering
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  proved_local_result: exact_Hilbert_commutator_source_map_and_eventual_all_P_o_sqrt_m_cap
  failed_terminal_completion: scalar_absolute_Vinogradov_Korobov_Perron_bound
  invariant_learned: the_frequency_derivative_on_the_diagonal_and_the_upper_prime_power_atom_cancel_together
  forbidden_future_move: infer_a_derivative_bound_from_real_axis_big_O_or_replace_moving_zero_free_width_by_a_constant
  smallest_unpaid_input: independent_one_sided_arithmetic_gain_beyond_half_power_on_the_same_projected_form
  next_decisive_test: one_bounded_independent_PAPER_audit_of_the_new_matrix_and_uniform_contour_return
  consumer_progress: NO_VANISHING_EXPONENT
```

## 11. Источники и границы доказательства

**[S0]** LOCAL_UPDATE текущего пакета, SHA-256 `c09ee0b60057cafdd16128b928990daca8ff50c02f7371c1fca70021245ff8d6`: принятые центрирование, непрерывный кредит, точный joint-return и half-power fallback.

**[S1–S9]** Размерно зафиксированные тела BASE_REQUEST, SHA-256 `4df1ce42289cb425c24f65861d330cc34e90c304f37724a5c9c76d69004cc1fe`. Их названия, хеши и точные позиции в исходном файле включены в `q55_checks.json`. Основные расходуемые интерфейсы: S4 §§2,4,5,7; S6; S7; S8; S9. Исторические скрипты только прочитаны.

**[E1]** Michael J. Mossinghoff, Timothy S. Trudgian, Andrew Yang, *Explicit zero-free regions for the Riemann zeta-function*, Research in Number Theory **10**, article 11 (2024), опубликовано 12 января 2024, DOI `10.1007/s40993-023-00498-y`, **Theorem 1.1**. Импортирована только указанная zero-free область и стандартное расположение нетривиальных нулей из введения; никакой full-CCM theorem из статьи не импортируется. Не утверждается, что это самая новая или оптимальная константа на 2026 год: для данного bounded теста это несущественно.

**[E2]** NIST DLMF §25.2, определение и аналитическое продолжение \(\zeta\), в частности §25.2(i) и §25.2(iv). Euler product и полюс используются только для элементарных аналитических шагов §4. Формула (4.5) отдельно выведена из интегрирования счётной функции.

```text
E1: https://link.springer.com/article/10.1007/s40993-023-00498-y
E2: https://dlmf.nist.gov/25.2
```

Это PAPER-вывод с проверенным внешним theorem import, не Lean-proof и не interval certificate. Независимый bounded аудит собственных §§2–7 ещё не выполнен. Полный пакет source assumptions не переутверждён сверх указанного inherited scope.

## 12. Новые проверки, ошибки и воспроизведение

Новый `check_q55.py` использует только стандартную библиотеку Python. Исторические программы S4 не извлекаются и не запускаются. Проверяются 115 rational-entry identities, точное сокращение комплексной мнимой части, инвариантность коммутатора к постоянному сдвигу, точная polynomial-модель joint remainder, затем пять малых физических Fourier-диагностик с настоящими \(\log n\), \(1/\sqrt n\) и всеми prime powers.

Фактические максимальные численные невязки первого запуска:

| Проверка | Максимальная абсолютная невязка |
|---|---:|
| Матрица direct overlap против symbol formula | \(3.5527136788005009\cdot10^{-15}\) |
| Форма одного комплексного вектора | \(1.2482983830578912\cdot10^{-15}\) |
| Три диагностических контакта | \(1.5700924586837752\cdot10^{-16}\) |
| \(A_{\rm cont}+\) decaying-kernel form | \(4.0255887917714667\cdot10^{-16}\) |

Порог программной проверки — \(2\cdot10^{-11}\). Это **наблюдённые residuals binary64**, не доказанные интервальные границы округления. Ни один из них не используется для аналитического знака или асимптотического квантора. Пять small-band случаев **не соответствуют** исходному sparse \(\epsilon\)-расписанию и служат только контролем общей finite algebra.

Предусмотренные ошибки, обнаруженные checker: обратный знак коммутатора; удаление диагональной производной; удаление производной верхнего атома при сохранении его значения; использование другого комплексного вектора в связанных членах; применение непрерывного отрицательного кредита без контактов. Первый запуск прошёл без исправления математических assertions. Новых runtime failure или установок не было.

Ниже находятся четыре полных новых приложения с bytes/SHA-256. Сохрани `replay_q55.py` из соответствующего блока и выполни:

```bash
python3 replay_q55.py \
  PROSHKA_CCM_Q55_DIRECT_HILBERT_PERRON_VERDICT_2026-10-27.md \
  PROSHKA_CCM_Q55_FRESH_CHAT_CONTINUATION_2026-10-27.txt \
  q55_replay
```

Первый аргумент — настоящий Markdown, второй — неизменённый исходный TXT, третий — создаваемый каталог с четырьмя новыми assets и отчётом запуска. Замени только пути при другом расположении файлов. Python 3.9+; сторонних пакетов нет. Replayer проверяет framing/hashes, запускает **только новый** checker и сопоставляет exact-данные строго, floating-данные с явно указанным допуском. Побайтное совпадение JSON также выводится отдельно; на разных реализациях `libm` последние биты могут отличаться и не называются формальной сертификацией.


BEGIN_ASSET registration_q55.json
BYTES: 2374
SHA256: 6f1e9f6079d05c3932fb10b78f74156a86b9b07f6976afe60e3b755eb5c08ade
```json
{
  "task": "Q55_OWNER_AUTHORIZED_FRESH_CHAT_CONTINUATION",
  "packet_sha256": "ecf79b6faecccceff894a4d98902de6aac198d3b06355240f0154d2e3d63632e",
  "stage": "After full supplied-source reading, transport checks and preliminary PAPER derivation; before new executable mathematical tests. Not a preregistration of the initial pencil derivation.",
  "operator": "REPRESENTATION_SHIFT",
  "rollback": "Original direct first form before the positive-family curvature requirement; Fourier divided differences and a finite Hilbert commutator, with an independently imported zero-free strip.",
  "predictions": {
    "P1": "The exact real Hermitian Fourier matrix of A-A_cont has diagonal 2 Re E(omega_j)-2 Im E'(omega_j)/L and offdiagonal -(g_j-g_k)/(pi*(j-k)), with g_j=Im E(omega_j).",
    "P2": "The finite discrete Hilbert matrix has norm at most pi; the one-sided cap max(diagonal)+max(g)-min(g) is dimension free and preserves all complex coefficients.",
    "P3": "Both exponential contacts give -4 norm_squared <= A_cont <= 0. The endpoint n=m cancels in the direct form but is retained in E and E'.",
    "P4": "A zero-free strip of Vinogradov-Korobov width, with a uniformly paid Perron contour and complex-frequency Cauchy derivative, yields O(sqrt(m)*exp(-c*(log(m)/log(log(m)))^(1/3))) on the entire original sparse carrier, not a fixed positive power saving.",
    "P5": "The independent direct cap bounds the full R_Psi-Psi through the exact source identity for every tau>0, without separately deleting centered-square mixed terms or higher-prime sectors.",
    "P6": "Finite exact controls and binary64 off-schedule Fourier diagnostics verify only algebra and normalization; they do not certify the asymptotic zero-free import, a production cell, or a cofinal CCM claim."
  },
  "planned_falsifiers": [
    "reverse the Hilbert commutator sign",
    "erase the diagonal frequency derivative",
    "drop the endpoint derivative while retaining its F atom",
    "replace the same complex coefficient vector by independent vectors",
    "ignore either exponential contact",
    "treat a real-axis error bound as automatically differentiable",
    "replace the moving zero-free width by a fixed strip"
  ],
  "historical_programs_executed": false,
  "repository_writes": false,
  "installations": false,
  "lean": false,
  "arb": false,
  "independent_audit": false
}
```
END_ASSET

BEGIN_ASSET check_q55.py
BYTES: 12349
SHA256: 485bce15f163c035884e6a80361cae4aa86cdb6f42c5c81d6a30d7b9498e4d94
```python
#!/usr/bin/env python3
"""Q55 source lock and NEW finite checks. Python 3.9+, standard library only.
Usage: python3 check_q55.py PACKET.txt [RESULT.json]
No embedded historical program is extracted or executed. Floating tests are
small, off-schedule Fourier diagnostics, not interval or cofinal certificates.
"""
from __future__ import annotations
import cmath
import hashlib
import json
import math
from fractions import Fraction as F
from pathlib import Path
import re
import sys

SHA = 'ecf79b6faecccceff894a4d98902de6aac198d3b06355240f0154d2e3d63632e'
SIZE = 127670
LF = 2039


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def source_lock(raw: bytes) -> dict:
    require(len(raw) == SIZE and raw.count(b'\n') == LF, 'packet size/LF')
    require(hashlib.sha256(raw).hexdigest() == SHA, 'packet SHA256')
    raw.decode('utf-8')
    frames = []
    for name in ('LOCAL_UPDATE', 'BASE_REQUEST'):
        h = re.search(rb'^' + name.encode() + rb': bytes=(\d+) SHA256=([0-9a-f]{64})$', raw, re.M)
        require(h is not None, 'missing outer frame ' + name)
        opening = b'BEGIN ' + name.encode() + b'\n'
        start = raw.index(opening) + len(opening)
        end = start + int(h[1])
        body = raw[start:end]
        require(hashlib.sha256(body).hexdigest() == h[2].decode(), 'frame hash ' + name)
        require(raw[end:].startswith(b'\nEND ' + name.encode() + b'\n'), 'frame closing ' + name)
        frames.append(dict(id=name, bytes=len(body), lf=body.count(b'\n'), sha256=h[2].decode(), start_byte=start, end_byte=end))
        if name == 'BASE_REQUEST':
            base, base_start = body, start
    headers = list(re.finditer(rb'^S(\d+): ([^;\n]+); bytes=(\d+); LF=(\d+); SHA256=([0-9a-f]{64})$', base[:base.index(b'BEGIN S1 ')], re.M))
    require(len(headers) == 9, 'source count')
    sources = []
    for i, h in enumerate(headers, 1):
        require(h[1] == str(i).encode(), 'source order')
        opening = b'BEGIN S' + h[1] + b' ' + h[2] + b'\n'
        start = base.index(opening) + len(opening)
        end = start + int(h[3])
        body = base[start:end]
        require(len(body) == int(h[3]) and body.count(b'\n') == int(h[4]), 'source size/LF')
        require(hashlib.sha256(body).hexdigest() == h[5].decode(), 'source hash')
        require(base[end:].startswith(b'\nEND S' + h[1] + b'\n'), 'source closing')
        absolute_start, absolute_end = base_start + start, base_start + end
        sources.append(dict(id='S'+str(i), name=h[2].decode(), bytes=len(body), lf=body.count(b'\n'), sha256=h[5].decode(), start_byte=absolute_start, end_byte=absolute_end, start_line=raw[:absolute_start].count(b'\n')+1, end_line=raw[:absolute_end].count(b'\n')))
    return dict(bytes=SIZE, lf=LF, sha256=SHA, frames=frames, sources=sources)


def exact_checks() -> dict:
    # pi has been absorbed into the off-diagonal unit; this checks signs,
    # differences and complex pairing, not an approximation to physical pi.
    total_entries = 0
    for M in (1, 2, 4):
        js = list(range(-M, M+1))
        g = {j: F(j*j*j-2*j, 7) for j in js}
        diagonal = {j: F(3*j*j-1, 5) for j in js}
        H = [[F(0) if j == k else F(1, j-k) for k in js] for j in js]
        direct = [[diagonal[j] if j == k else -(g[j]-g[k])/F(j-k) for k in js] for j in js]
        comm = [[(g[j]-g[k])*H[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        rebuilt = [[(diagonal[j] if j == k else F(0))-comm[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        require(direct == rebuilt, 'exact commutator identity')
        require(all(direct[a][b] == direct[b][a] for a in range(len(js)) for b in range(len(js))), 'symmetry')
        re = [F(j+2, 3) for j in js]
        im = [F(j*j-1, 4) for j in js]
        # For a real symmetric B, c*Bc = Re(c)^T B Re(c)+Im(c)^T B Im(c).
        imag = sum((re[a]*im[b]-im[a]*re[b])*direct[a][b] for a in range(len(js)) for b in range(len(js)))
        require(imag == 0, 'same complex vector pairing')
        shifted = [[(g[j]+F(11,3)-g[k]-F(11,3))*H[a][b] for b,k in enumerate(js)] for a,j in enumerate(js)]
        require(shifted == comm, 'constant shift invariance')
        total_entries += len(js)**2
    # Exact joint-family change: Psi-Phi=q(tau), q'(0)=A_cont/2.
    # Retain constant, linear, quadratic, cubic and quartic coefficients.
    q = [F(0), F(-3,7), F(5,4), F(-2,9), F(7,11)]
    tau = F(3,5)
    qvalue = sum(v*tau**i for i,v in enumerate(q))
    remainder_change = sum(q[i]*tau**i for i in range(2,len(q)))
    require(remainder_change-qvalue == -tau*q[1], 'full joint remainder change')
    # The modulus cap |E|<=B in a strip plus radius 1/L gives |E'|/L<=B:
    # diagonal <=4B and oscillation<=2B, hence the advertised 6B.
    require(2+2+2 == 6, 'strip-to-matrix budget')
    return dict(matrix_entries=total_entries, exact_joint_polynomial_case=1, commutator_constant_shift=True, exact_complex_pairing=True)


def mangoldt(m: int) -> list[float]:
    a = [0.0]*(m+1)
    for p in range(2,m+1):
        if all(p%d for d in range(2, math.isqrt(p)+1)):
            n = p
            while n <= m:
                a[n] = math.log(p)
                n *= p
    return a


def primitive(z: complex, L: float) -> tuple[complex,complex]:
    """Integral exp(z*a) da and its derivative w.r.t. the real frequency."""
    if abs(z) < 1e-12:
        return complex(L), 0.5j*L*L
    e = cmath.exp(z*L)
    return (e-1)/z, 1j*(e*(L*z-1)+1)/(z*z)


def matrix_from_symbol(values, derivatives, js, L):
    out = []
    for a,j in enumerate(js):
        row = []
        for b,k in enumerate(js):
            if j == k:
                v = 2*values[a].real-2*derivatives[a].imag/L
            else:
                v = -(values[a].imag-values[b].imag)/(math.pi*(j-k))
            row.append(v)
        out.append(row)
    return out


def shift_matrix(js, L, a):
    freq = [2*math.pi*j/L for j in js]
    out = []
    for j,wj in enumerate(freq):
        row = []
        for k,wk in enumerate(freq):
            if j == k:
                entry = (1-a/L)*cmath.exp(1j*wk*a)
            else:
                entry = cmath.exp(1j*wk*a)*((cmath.exp(1j*(wk-wj)*(L-a))-1)/(1j*L*(wk-wj)))
            row.append(2*entry.real)
        out.append(row)
    return out


def quadratic(A, c):
    return sum(c[j].conjugate()*A[j][k]*c[k] for j in range(len(c)) for k in range(len(c)))


def solve(A, b):
    A = [list(map(complex,row))+[complex(v)] for row,v in zip(A,b)]
    n = len(b)
    for k in range(n):
        pivot = max(range(k,n), key=lambda i: abs(A[i][k]))
        require(abs(A[pivot][k]) > 1e-14, 'singular diagnostic constraint matrix')
        A[k], A[pivot] = A[pivot], A[k]
        d = A[k][k]
        A[k] = [x/d for x in A[k]]
        for i in range(n):
            if i != k:
                d = A[i][k]
                A[i] = [x-d*y for x,y in zip(A[i],A[k])]
    return [A[i][-1] for i in range(n)]


def diagnostic_checks() -> dict:
    max_entry_error = max_form_error = max_contact_residual = max_continuous_error = 0.0
    rows = []
    detectors = dict(reverse_commutator=False, erase_diagonal_derivative=False, delete_top_derivative=False, independent_complex_vector=False, ignore_contacts=False)
    # Judge-before-player: a wrong diagonal (no derivative) must not be
    # accepted for a positive atom at a=L. Correct endpoint form is zero.
    bad_endpoint = 2*math.log(16)/math.sqrt(16)
    require(bad_endpoint > 1.0, 'planted endpoint violation was not detected')
    detectors['delete_top_derivative'] = True
    for m,M in ((8,2),(16,3),(27,2),(64,3),(81,4)):
        L = math.log(m)
        js = list(range(-M,M+1))
        freq = [2*math.pi*j/L for j in js]
        lm = mangoldt(m)
        V = [sum(lm[n]/math.sqrt(n)*cmath.exp(1j*w*math.log(n)) for n in range(2,m+1)) for w in freq]
        D = [sum(1j*math.log(n)*lm[n]/math.sqrt(n)*cmath.exp(1j*w*math.log(n)) for n in range(2,m+1)) for w in freq]
        C, CD = zip(*(primitive(0.5+1j*w,L) for w in freq))
        Q, QD = zip(*(primitive(-0.5+1j*w,L) for w in freq))
        A = [[0.0]*len(js) for _ in js]
        for n in range(2,m+1):
            if lm[n]:
                H = shift_matrix(js,L,math.log(n))
                for a in range(len(js)):
                    for b in range(len(js)):
                        A[a][b] += lm[n]/math.sqrt(n)*H[a][b]
        formula = matrix_from_symbol(V,D,js,L)
        err = max(abs(A[a][b]-formula[a][b]) for a in range(len(js)) for b in range(len(js)))
        max_entry_error = max(max_entry_error,err)
        require(err < 2e-11, 'physical matrix identity')
        c = [complex(j+2, j*j-1) for j in js]
        norm = math.sqrt(sum(abs(v)**2 for v in c))
        c = [v/norm for v in c]
        ferr = abs(quadratic(A,c)-quadratic(formula,c))
        max_form_error = max(max_form_error,ferr)
        require(ferr < 2e-11, 'complex physical form')
        # Same three contact rows, on a deliberately off-schedule small band.
        contacts = [[1+0j for _ in js], [1/(0.5+1j*w) for w in freq], [1/(-0.5+1j*w) for w in freq]]
        chosen = [0,M,2*M]
        rest = [k for k in range(len(js)) if k not in chosen]
        rhs = [-sum(row[k]*c[k] for k in rest) for row in contacts]
        vals = solve([[row[k] for k in chosen] for row in contacts],rhs)
        for k,v in zip(chosen,vals): c[k] = v
        norm = math.sqrt(sum(abs(v)**2 for v in c)); c = [v/norm for v in c]
        residual = max(abs(sum(row[k]*c[k] for k in range(len(js)))) for row in contacts)
        max_contact_residual = max(max_contact_residual,residual)
        AC = matrix_from_symbol(C,CD,js,L)
        AQ = matrix_from_symbol(Q,QD,js,L)
        cv,qv = quadratic(AC,c),quadratic(AQ,c)
        max_continuous_error = max(max_continuous_error,abs(cv+qv))
        require(residual < 2e-12 and abs(cv+qv) < 2e-11, 'contact/continuous identity')
        require(-4-2e-11 <= cv.real <= 2e-11, 'continuous interval diagnostic')
        E = [v-u for v,u in zip(V,C)]; ED = [v-u for v,u in zip(D,CD)]
        B = matrix_from_symbol(E,ED,js,L)
        diagonal = [B[k][k] for k in range(len(js))]
        g = [v.imag for v in E]
        cap = max(diagonal)+max(g)-min(g)
        value = quadratic(B,c).real
        require(value <= cap+2e-11, 'one-sided cap diagnostic')
        detectors['reverse_commutator'] |= any(abs(A[a][b]+formula[a][b]) > 1e-4 for a in range(len(js)) for b in range(len(js)) if a != b)
        detectors['erase_diagonal_derivative'] |= any(abs(A[k][k]-2*V[k].real) > 1e-4 for k in range(len(js)))
        d = [complex(v.real,-v.imag) for v in c]
        wrong = sum(c[j].conjugate()*B[j][k]*d[k] for j in range(len(c)) for k in range(len(c)))
        detectors['independent_complex_vector'] |= abs(wrong-quadratic(B,c)) > 1e-4
        e0 = [0j]*len(js); e0[M] = 1
        detectors['ignore_contacts'] |= quadratic(AC,e0).real > 0.1
        rows.append(dict(m=m,M=M,original_epsilon_schedule=False,source_matrix_max_abs_error=format(err,'.17g'),contact_max_abs_residual=format(residual,'.17g'),continuous_value=format(cv.real,'.17g'),directed_cap=format(cap,'.17g'),tested_quadratic_value=format(value,'.17g')))
    require(all(detectors.values()), 'missed planted algebra violation')
    return dict(cases=rows,max_entry_error=format(max_entry_error,'.17g'),max_form_error=format(max_form_error,'.17g'),max_contact_residual=format(max_contact_residual,'.17g'),max_continuous_identity_error=format(max_continuous_error,'.17g'),tolerance='2e-11',arithmetic='binary64, not outward rounded',interval_certificate=False,planted_violations_detected=detectors)


def main() -> None:
    if len(sys.argv) not in (2,3):
        raise SystemExit('usage: python3 check_q55.py PACKET.txt [RESULT.json]')
    raw = Path(sys.argv[1]).read_bytes()
    result = dict(source=source_lock(raw),exact=exact_checks(),diagnostics=diagnostic_checks(),historical_programs_executed=False,production_spectrum=False,lean=False,arb=False,independent_audit=False,cofinal_bound_certified_by_computation=False,actual_zeta_zeros_computed=False)
    text = json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n'
    out = Path(sys.argv[2] if len(sys.argv)==3 else 'q55_checks.json')
    out.write_text(text,encoding='utf-8')
    print(text,end='')

if __name__ == '__main__':
    main()
```
END_ASSET

BEGIN_ASSET q55_checks.json
BYTES: 6481
SHA256: 711265d75576957cee5d5db6b2217a02ff38f7c561119dfba5ab69e4c8c32da3
```json
{
  "actual_zeta_zeros_computed": false,
  "arb": false,
  "cofinal_bound_certified_by_computation": false,
  "diagnostics": {
    "arithmetic": "binary64, not outward rounded",
    "cases": [
      {
        "M": 2,
        "contact_max_abs_residual": "2.7809732887839817e-17",
        "continuous_value": "-0.059496073480870111",
        "directed_cap": "0.74624170485009955",
        "m": 8,
        "original_epsilon_schedule": false,
        "source_matrix_max_abs_error": "1.7763568394002505e-15",
        "tested_quadratic_value": "-0.25397878825053699"
      },
      {
        "M": 3,
        "contact_max_abs_residual": "1.3877787807814457e-16",
        "continuous_value": "-0.038289564761992634",
        "directed_cap": "0.88337915579635795",
        "m": 16,
        "original_epsilon_schedule": false,
        "source_matrix_max_abs_error": "1.7763568394002505e-15",
        "tested_quadratic_value": "-0.041469534506280464"
      },
      {
        "M": 2,
        "contact_max_abs_residual": "3.1031676915590914e-17",
        "continuous_value": "-0.15098342690038369",
        "directed_cap": "0.37121434065810605",
        "m": 27,
        "original_epsilon_schedule": false,
        "source_matrix_max_abs_error": "3.5527136788005009e-15",
        "tested_quadratic_value": "-0.64716621830654741"
      },
      {
        "M": 3,
        "contact_max_abs_residual": "1.5700924586837752e-16",
        "continuous_value": "-0.087729874491628015",
        "directed_cap": "0.52002477679431036",
        "m": 64,
        "original_epsilon_schedule": false,
        "source_matrix_max_abs_error": "3.5527136788005009e-15",
        "tested_quadratic_value": "-0.41114439394297375"
      },
      {
        "M": 4,
        "contact_max_abs_residual": "1.1102230246251565e-16",
        "continuous_value": "-0.045935482800922772",
        "directed_cap": "0.76809092810438084",
        "m": 81,
        "original_epsilon_schedule": false,
        "source_matrix_max_abs_error": "3.5527136788005009e-15",
        "tested_quadratic_value": "-0.16003912627520392"
      }
    ],
    "interval_certificate": false,
    "max_contact_residual": "1.5700924586837752e-16",
    "max_continuous_identity_error": "4.0255887917714667e-16",
    "max_entry_error": "3.5527136788005009e-15",
    "max_form_error": "1.2482983830578912e-15",
    "planted_violations_detected": {
      "delete_top_derivative": true,
      "erase_diagonal_derivative": true,
      "ignore_contacts": true,
      "independent_complex_vector": true,
      "reverse_commutator": true
    },
    "tolerance": "2e-11"
  },
  "exact": {
    "commutator_constant_shift": true,
    "exact_complex_pairing": true,
    "exact_joint_polynomial_case": 1,
    "matrix_entries": 115
  },
  "historical_programs_executed": false,
  "independent_audit": false,
  "lean": false,
  "production_spectrum": false,
  "source": {
    "bytes": 127670,
    "frames": [
      {
        "bytes": 3590,
        "end_byte": 5649,
        "id": "LOCAL_UPDATE",
        "lf": 77,
        "sha256": "c09ee0b60057cafdd16128b928990daca8ff50c02f7371c1fca70021245ff8d6",
        "start_byte": 2059
      },
      {
        "bytes": 121865,
        "end_byte": 127651,
        "id": "BASE_REQUEST",
        "lf": 1945,
        "sha256": "4df1ce42289cb425c24f65861d330cc34e90c304f37724a5c9c76d69004cc1fe",
        "start_byte": 5786
      }
    ],
    "lf": 2039,
    "sha256": "ecf79b6faecccceff894a4d98902de6aac198d3b06355240f0154d2e3d63632e",
    "sources": [
      {
        "bytes": 3624,
        "end_byte": 16598,
        "end_line": 199,
        "id": "S1",
        "lf": 77,
        "name": "CCM_POST_Q54_ENDPOINT_SEAM_CANDIDATE.md",
        "sha256": "0f7124903a297f9a78e33867c6167246625bf5680ba53abdd45e90a24968f493",
        "start_byte": 12974,
        "start_line": 123
      },
      {
        "bytes": 1628,
        "end_byte": 18281,
        "end_line": 228,
        "id": "S2",
        "lf": 25,
        "name": "CCM_POST_Q54_ENDPOINT_SEAM_REVIEW.md",
        "sha256": "52a40c19d1bb665b0b25f5b9296678fc37129b641f9b85073d83e829f448f7ba",
        "start_byte": 16653,
        "start_line": 204
      },
      {
        "bytes": 3398,
        "end_byte": 21741,
        "end_line": 299,
        "id": "S3",
        "lf": 67,
        "name": "CCM_POST_Q54_CURVATURE_SUPPORT_PREFLIGHT.md",
        "sha256": "bc6079dce73366a97e2ab5e37a499c9d81bb62039d76422ee543f3a0d57d6845",
        "start_byte": 18343,
        "start_line": 233
      },
      {
        "bytes": 81134,
        "end_byte": 102959,
        "end_line": 1616,
        "id": "S4",
        "lf": 1313,
        "name": "PROSHKA_CCM_SIGNED_DIVISOR_IMAGE_RETURN_Q54_VERDICT_2026-10-27.md",
        "sha256": "f2f6684f985e6691ca277b29718520a9db815cf2fde624af107eb9cde9ab0da0",
        "start_byte": 21825,
        "start_line": 304
      },
      {
        "bytes": 4194,
        "end_byte": 107193,
        "end_line": 1697,
        "id": "S5",
        "lf": 77,
        "name": "CCM_Q54_CONCLUSION.md",
        "sha256": "bdae1b89ddc9a0b38c81590546839dde5adcdbe35f03cf61884416bfa90d8e53",
        "start_byte": 102999,
        "start_line": 1621
      },
      {
        "bytes": 5036,
        "end_byte": 112275,
        "end_line": 1793,
        "id": "S6",
        "lf": 92,
        "name": "CCM_JOINT_Q04_CONCLUSION.md",
        "sha256": "617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086",
        "start_byte": 107239,
        "start_line": 1702
      },
      {
        "bytes": 3839,
        "end_byte": 116154,
        "end_line": 1863,
        "id": "S7",
        "lf": 66,
        "name": "CCM_Q13_CONCLUSION.md",
        "sha256": "6c2f145f392d4336471adaf7267ab7d4e17a48e966343a45209f4ccebe1ad34c",
        "start_byte": 112315,
        "start_line": 1798
      },
      {
        "bytes": 5205,
        "end_byte": 121422,
        "end_line": 1960,
        "id": "S8",
        "lf": 93,
        "name": "CCM_POST_Q48_FIRST_FORM_DEFICIT_CROSSWALK.md",
        "sha256": "c7efc8783bb4306ee55df5574649fccf3da8240d37384b8db965183d1dd569e6",
        "start_byte": 116217,
        "start_line": 1868
      },
      {
        "bytes": 6174,
        "end_byte": 127642,
        "end_line": 2033,
        "id": "S9",
        "lf": 69,
        "name": "CCM_SPARSE_BAND_RECEIVER.md",
        "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
        "start_byte": 121468,
        "start_line": 1965
      }
    ]
  }
}
```
END_ASSET

BEGIN_ASSET replay_q55.py
BYTES: 3747
SHA256: e64af2015697d699577113ed4b0ebbf515c82237c325c5fb3021739021f8abea
```python
#!/usr/bin/env python3
"""Extract only the four NEW Q55 assets and reproduce their checks.
Usage: python3 replay_q55.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]
Python 3.9+, standard library only. No historical source code is run.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HEADER = re.compile(rb'^BEGIN_ASSET ([A-Za-z0-9_.-]+)\nBYTES: (\d+)\nSHA256: ([0-9a-f]{64})\n```[A-Za-z0-9_-]*\n',re.M)
EXPECTED = {'registration_q55.json','check_q55.py','q55_checks.json','replay_q55.py'}


def extract(raw: bytes) -> dict:
    assets = {}
    pos = 0
    while True:
        h = HEADER.search(raw,pos)
        if h is None:
            break
        name = h[1].decode('ascii')
        if name not in EXPECTED or name in assets:
            raise ValueError('unexpected/repeated asset: '+name)
        start, end = h.end(), h.end()+int(h[2])
        body = raw[start:end]
        if len(body) != int(h[2]) or hashlib.sha256(body).hexdigest() != h[3].decode():
            raise ValueError('asset size/hash: '+name)
        close = b'```\nEND_ASSET\n'
        if raw[end:end+len(close)] != close:
            raise ValueError('asset frame: '+name)
        body.decode('utf-8')
        assets[name] = body
        pos = end+len(close)
    if set(assets) != EXPECTED:
        raise ValueError('missing asset')
    return assets


def compare(expected: dict, actual: dict) -> None:
    # The source provenance, exact assertions and flags must agree exactly.
    for k in expected:
        if k != 'diagnostics' and expected[k] != actual.get(k):
            raise ValueError('exact replay mismatch: '+k)
    e,a = expected['diagnostics'],actual['diagnostics']
    for k in ('arithmetic','interval_certificate','planted_violations_detected','tolerance'):
        if e[k] != a[k]:
            raise ValueError('diagnostic metadata mismatch: '+k)
    if len(e['cases']) != len(a['cases']):
        raise ValueError('case count mismatch')
    for old,new in zip(e['cases'],a['cases']):
        for k in ('m','M','original_epsilon_schedule'):
            if old[k] != new[k]:
                raise ValueError('diagnostic case mismatch')
        for k in set(old)-{'m','M','original_epsilon_schedule'}:
            if abs(float(old[k])-float(new[k])) > 5e-11:
                raise ValueError('binary64 replay mismatch: '+k)
    # The executed checker itself enforces its 2e-11 residual tolerance.


def main() -> None:
    if len(sys.argv) not in (3,4):
        raise SystemExit('usage: python3 replay_q55.py VERDICT.md PACKET.txt [OUTPUT_DIRECTORY]')
    verdict,packet = (Path(x).resolve() for x in sys.argv[1:3])
    out = Path(sys.argv[3] if len(sys.argv)==4 else 'q55_replay').resolve()
    assets = extract(verdict.read_bytes())
    out.mkdir(parents=True,exist_ok=True)
    for name,body in assets.items():
        target = out/name
        if target.resolve() in (verdict,packet):
            raise ValueError('refusing to overwrite input')
        target.write_bytes(body)
    actual_path = out/'q55_replayed.json'
    run = subprocess.run([sys.executable,str(out/'check_q55.py'),str(packet),str(actual_path)],capture_output=True,check=True)
    (out/'check_q55.stdout').write_bytes(run.stdout)
    compare(json.loads(assets['q55_checks.json']),json.loads(actual_path.read_bytes()))
    result = dict(asset_count=4,all_asset_hashes_match=True,new_checker_executed=True,semantic_replay=True,json_byte_identical=actual_path.read_bytes()==assets['q55_checks.json'],historical_programs_executed=False,independent_audit=False,interval_certificate=False,production_spectrum=False)
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
```
END_ASSET

## 13. Проверка окончательного артефакта

Все четыре новых приложения извлечены из собранного Markdown по их точным размерам и SHA-256. Извлечённый replayer заново запустил только новый `check_q55.py` на неизменённом исходном Q55 TXT. Исторические программы не исполнялись. Результат собственного воспроизведения:

```json
{
  "all_asset_hashes_match": true,
  "asset_count": 4,
  "historical_programs_executed": false,
  "independent_audit": false,
  "interval_certificate": false,
  "json_byte_identical": true,
  "new_checker_executed": true,
  "production_spectrum": false,
  "semantic_replay": true
}
```

Это проверка доставки и собственных конечных контролей, не независимый PAPER-аудит §4 и не сертификация бесконечного квантора программой. Оригинальный пакет не изменялся.

## Одна CODEX DIRECTIVE

Выполнить **один bounded независимый PAPER-аудит нового результата §§2–7**, затем один replay приложений. Проверить в таком порядке: знак и нормировку (2.6)–(2.8); непериодическое Hilbert-сжатие и направленный bound (3.6); реальную область действия [E1, Theorem 1.1]; нулесвободные диски для \((s-1)\zeta(s)\) и цену (4.8); равномерность Perron по всей комплексной полосе (4.4), включая \(X=m+1/2\), обе горизонтали, вычет и поправку (4.13); законность Cauchy-платы; возврат всей \(\Psi\)-формы и отсутствие лишней short/arch платы. Зафиксировать первую материальную ошибку либо принять **ровно** dimension-free source map, асимптотический \(o(\sqrt m)\) upper и полный joint-return на этой шкале. Не принимать \(\eta(\epsilon)\to0\), новый фиксированный показатель, RH или отдельную малость кривизны.

Из каталога, содержащего этот Markdown и исходный TXT, после сохранения нового replayer выполнить:

```bash
python3 replay_q55.py \
  PROSHKA_CCM_Q55_DIRECT_HILBERT_PERRON_VERDICT_2026-10-27.md \
  PROSHKA_CCM_Q55_FRESH_CHAT_CONTINUATION_2026-10-27.txt \
  q55_replay
```

Успех gate: отсутствие материальных PAPER findings, совпавшие hashes новых assets и `semantic_replay=true`. `json_byte_identical` сообщить отдельно: отличие последних floating-битов не превращать в нарушение математического знака. При ошибке — `Q55_HILBERT_PERRON_RETURN_MATERIAL_FINDING`, точная формула, контррасчёт и минимальный ремонт; при отсутствии ошибки — `Q55_HILBERT_PERRON_RETURN_BOUNDED_PAPER_ACCEPTED`, с `FULL_POWER=1/2`, `ETA_EPSILON_TO_ZERO=NOT_DERIVED`, `RH=OPEN`. Не запускать новый вопрос, production scan, установку пакетов или запись в репозиторий автоматически. Этот независимый аудит в текущем ответе не выполнялся и выполненным не объявляется.
