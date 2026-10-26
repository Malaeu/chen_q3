# STATUS: TRY_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42
```yaml
OPERATIVE_CLASS: TRY_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42
REQUEST_ID: Q42_COFINAL_SHORT_MOBIUS_JOINT
DATE: '2026-10-26'
VERDICT_CODE: COFINAL_JOINT_MOMENT_CONTROL_POLE_HIERARCHY_REPAIRED_FINITE_SIGN_OPEN
REQUEST_COMPLETION: EXECUTED_PARTIAL_NO_FULL_SIGNED_UPPER
PROGRESS_CLASS: NO_PROGRESS
PRIMARY_CONSUMER: OPEN
AUXILIARY_RESULT: UNIFORM_ACTUAL_MOMENT_BOUND_AND_EXACT_MASS_BALANCED_RETURN
SOURCE: ORIGINAL_FULL_CCM_ORIGINAL_THREE_CONTACT_SPARSE_BAND
SCHEDULE: 'N=m; L=log(m); M=R=floor(m^epsilon); fixed 0<epsilon<1/32'
REQUEST_BYTES: 117726
REQUEST_LF: 2030
REQUEST_SHA256: d4ce7e99338317abb4382a00f0baaa5e6808221eb71543360b94b76535d444d6
BASE_COMMIT: 17621aa1ff8c70187f88401be2174ba0c1259dfd
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SOURCE_BODIES: 10
MANIFEST: ALL_BYTE_LF_SHA256_FRAMES_MATCH
EXTERNAL_INPUT: 'E1: unbounded U with U*abs(a_U)<=1/2, primary statement checked'
EXTERNAL_G_BOUND_14: NOT_ASSUMED
NEW_RH_ZF_MERTENS_VARIANCE_PREMISE: NONE
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
KILL_SCOPE: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
CLOSES: []
OPENS: []
RH: OPEN_NOT_CLAIMED
CF22_PYSR: PARKED_REOPENABLE
REPOSITORY_WRITES: false
HISTORICAL_CODE_EXECUTED: false
NEW_INDEPENDENT_AUDIT: false
LEAN: NOT_RUN
ARB_INTERVAL: NOT_RUN
PRODUCTION_SPECTRA: NOT_RUN
```

# Q42. Cofinal short-Möbius: совместные моменты, полный полюсный ремонт и конечный знаковый остаток

## 0. Результат и точная граница

**Нового верхнего знака для полной CCM не получено.** Есть новый вспомогательный количественный результат для **настоящих коротких моментов**, а не повтор оценки старшего полюса:

при
\[
 a_U=\sum_{d\le U}\frac{\mu(d)}d,\qquad U|a_U|\le\tfrac12,
 \qquad v=U+1,\quad U\ge64,
\]
доказано
\[
 \boxed{\left|1-M_U'(1)-a_U\log v\right|\le\frac45.}
 \tag{0.1}
\]
Более того, введённая ниже **одна явная коррекция за сохранённым префиксом** даёт контроль всех связанных производных на диске радиуса \((100\log v)^{-1}\), равномерно по растущему \(U\). Полная биномиальная сборка после этой коррекции имеет только простой полюс; его коэффициент \(\kappa_U\) удовлетворяет
\[
 \boxed{1-(4/5)^K\le\kappa_U\le1+(4/5)^K,\qquad\kappa_U>0.}
 \tag{0.2}
\]
После обеих временных сторон и исходного \(P\) этот полюс даёт **неположительную** матрицу \(-\kappa_U H_d\), а не большую отдельную цену.

Однако полный конечный остаток равен
\[
 \boxed{\mathcal F_{m,U}=C^0_m-(1-\kappa_U)H_d,\qquad
 \|\mathcal F_{m,U}-C^0_m\|\le4(4/5)^K.}
 \tag{0.3}
\]
**В нём прежняя \(C^0_m\) сохраняется с коэффициентом один.** Независимого малого верхнего знака этой матрицы не доказано. Поэтому (0.1)–(0.2) не объявляются выигрышем исходного CCM-потребителя.

Существенная граница: устранение всей искусственной полюсной иерархии возможно с точным finite return. Значит, сама эта иерархия не должна становиться новой обязательной стеной. Но устранить её — не значит оценить полную арифметическую форму.

Здесь не строится ещё один большой norm certificate ради no-go. Нет утверждения о невозможности CCM, о нижней цене её спектра или об отсутствии иных арифметических поставщиков. Полная безусловная оценка остаётся прежней; \(3/8\) остаётся условным на прежнюю ZF78.

---

## 1. Intake, действующие источники и внешняя предпосылка

Канонический TXT прочитан полностью, включая все десять тел и исторический код в S2. По байтам прикреплённого файла измерено:

```text
PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_2026-10-26.txt
117726 bytes
2030 LF
SHA256 d4ce7e99338317abb4382a00f0baaa5e6808221eb71543360b94b76535d444d6
```

Проверены все внутренние размеры, LF, SHA-256, UTF-8 и точные границы тел. Separator LF не включался в body. Краткая пользовательская подпись не задавала общий хеш; указанный выше хеш измерен, а не взят из предыдущего запроса. Таблица всех тел — в §11, машиночитаемый manifest — в приложении.

Bootstrap получен через GitHub connector из `Malaeu/chen_q3`, `rh_clean`, `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, blob указан в заголовке. Другие живые файлы для выбора задачи не сканировались. Репозиторий не изменялся. Исторические инструкции и скрипты не исполнялись.

### 1.1. Что используется из пакета

| Вход | Область использования | Чего не предполагаем |
|---|---|---|
| S1–S2 | Конечная short-inverse алгебра, исходный \(P\), signed Q32-map | Ни знак биномиальной суммы, ни малость её отдельных каналов |
| S3 | Нельзя повторно применять дешёвый constrained \(Z\) без возврата гипотез | Не оцениваем произведения как произведения сжатых операторов |
| S4 | Полная \(B+R=-\zeta'/\zeta\), поддержка \(R\), необходимость всех возвратов | Не удаляем residues из факта нулевой физической поддержки |
| S5 | Cofinal вход, первичный локатор; старшая-полюсная оценка уже известна | Не импортируем Theorem 3.1(14) |
| S6 | Область прежнего constrained inverse и условной ZF78 | Не итерируем \(Z\) на вышедших из \(P\) промежуточных векторах |
| S7–S8 | Уже оплаченные all-\(P\) contour и central returns | Не переносим их аналитические нормы бесплатно на новый бесконечный ряд |
| S9 | Условный sparse-band receiver на каждой достаточно поздней ячейке | Гипотетический нуль не объявляется найденным |
| S10 | Лучший приложенный fallback и граница результата на одной семье | Одно семейство не заменяет all-\(P\) квантор |

Хеши устанавливают тождественность текста, а не повторную сертификацию его доказательств.

### 1.2. E1 — проверенный scope первоисточника

**[COFINAL_FAMILY | PAPER, external theorem dependency]** На первичной странице Gallardo–Gutiérrez/Seco проверены Remark 3.2(e) и формула (16): из цитируемого результата С. Сельберга авторы получают неограниченное множество целых \(U\) с \(U|a_U|\le1/2\). Условие на \(G(n,U)\) в Theorem 3.1(14) остаётся **гипотезой**, не нашим входом. Доказательство исходной теоремы Сельберга заново не сертифицировано.

E1: E. A. Gallardo-Gutiérrez, D. Seco, *Zero-Free Regions of the Riemann Zeta Function and Approximation in Weighted Dirichlet Spaces*, Complex Analysis and Operator Theory 19, 38 (2025), DOI `10.1007/s11785-025-01661-2`. Первичная HTML-страница:

```text
https://link.springer.com/article/10.1007/s11785-025-01661-2
```

В этой работе проверялись именно HTML-формулы и область E1. Бинарный PDF и его checksum не заявляются проверенными. Никакой новой количественной PNT/Mertens-теоремы далее не требуется. Других внешних оценочных поставщиков не импортировано.

---

## 2. Исходный квантор и выбранный механизм

**[COFINAL_FAMILY | PAPER; inherited domain]** Сначала фиксируется
\[
 0<\epsilon<1/32,\qquad K=\lceil1/\epsilon\rceil.
\]
На неизменной производственной ячейке
\[
 N=m,\quad L=\log m,\quad M=R=\lfloor m^\epsilon\rfloor,
 \quad \Omega=2\pi M/L.
\]
\(F_M\) — прежний изометрический Fourier-синтез на \([0,L]\); \(P\) — прежний трёхконтактный проектор. Для \(c=Pc\), \(f=F_Mc\):
\[
 \|f\|_2=\|c\|_2,\qquad f(0)=f(L)=0,
 \qquad\int_0^L e^{\pm t/2}f(t)\,dt=0.
\]
Все векторы могут быть комплексными.

Сохраняем
\[
 A_m=\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}P Q_M(\log n)P,
 \qquad C^0_m=A_m+H_d,\qquad0\preceq H_d\preceq4P.
 \tag{2.1}
\]

### 2.1. Cofinal расписание общее для всех векторов

Для каждого достаточно большого \(U\) из E1 берём целое
\[
 U^{1/\epsilon}\le m<(U+1)^{1/\epsilon}.
 \tag{2.2}
\]
Длина этого интервала стремится к бесконечности, поэтому такое целое существует. Тогда \(R=M=U\), \((U+1)^K>m\), и последовательность \(m\) неограниченна. Она не зависит от \(c\) или \(W\).

Это именно разрешённый cofinal режим. Если бы на нём был независимо доказан требуемый upper, eventual witness из S9 действовал бы и на этой последовательности. Здесь такого upper нет.

### 2.2. Проверяемый ход

Малость одного \(a_U\) не означает малость всех \(M_U^{(r)}(1)\). Поэтому вместо бесплатной итерации \(Z\) или оплаты одного Laurent-коэффициента используем **полное балансирование короткого обратного ряда одним атомом в первом ещё не закреплённом индексе**:
\[
 v=U+1,\qquad \tau_U=v a_U,
\]
\[
 u_U(n)=\mu(n)\mathbf1_{n\le U},\qquad
 \widetilde u_U=u_U-\tau_U\delta_v.
 \tag{2.3}
\]
Это вспомогательный коэффициент, не замена функции Мёбиуса в исходной задаче. Ниже показано, что **после всей биномиальной сборки исходная \(\Lambda\) возвращается точно**, включая \(n=m\). Все члены с коррекцией, в том числе смешанные, обязательны.

На cofinal множестве
\[
 |\tau_U|\le\frac{U+1}{2U},\qquad
 \left\|\tau_U v^{-1/2}V_{\log v}\right\|
 \le\frac{\sqrt{U+1}}{2U}\le\frac1{\sqrt{2U}}.
 \tag{2.4}
\]
Последнее — только цена одного вспомогательного атома. Мы **не** умножаем её на якобы дешёвые нормы степеней \(Z\). Полная цена изменения конечной source-матрицы будет ровно нулевой по коэффициентам, а не по такой нормовой аргументации.

Использование \(v=U+1\), а не \(v=U\), существенно: сохраняется весь префикс \(1\le n\le U\), от которого зависит строгий гиперболический cutoff.

---

## 3. Новая количественная связь настоящих моментов

### 3.1. Точная примитивная функция, со всеми полами

**[ABSTRACT | PAPER]** Определим для вещественных \(x\ge1\)
\[
 \widetilde G_U(x)=
 \sum_{d\le U}\mu(d)\lfloor x/d\rfloor
 -\tau_U\lfloor x/v\rfloor,
 \qquad Q_U=\sum_{d\le U}\mu(d)^2.
 \tag{3.1}
\]
Здесь \(\widetilde G_U\) — накопленная сумма коэффициентов \(\mathbf1*\widetilde u_U\), а не сама последовательность этих коэффициентов. Смешивать эти два объекта нельзя.

Поскольку \(\tau_U/v=a_U\), линейные части полов сокращаются **до модуля**:
\[
 \boxed{\widetilde G_U(x)=
 -\sum_{d\le U}\mu(d)\{x/d\}+\tau_U\{x/v\}.}
 \tag{3.2}
\]
Кроме того, точное делительное свойство настоящей \(\mu\) даёт
\[
 \boxed{\widetilde G_U(x)=1\quad(1\le x<v).}
 \tag{3.3}
\]
Это включает нецелые \(x\); в точке \(v\) уже может быть скачок, который не удаляется.

Только после сокращения линейного члена получаем законную равномерную оценку
\[
 \boxed{|\widetilde G_U(x)|\le Q_U+|\tau_U|=:S_U.}
 \tag{3.4}
\]
Она не является Theorem 3.1(14). Её размер в общем случае \(O(U)\), не требуемый там более сильный диапазонный выигрыш.

### 3.2. Mellin-формула без неравномерного Laurent-предела

Положим
\[
 M_U(s)=\sum_{d\le U}\mu(d)d^{-s},\quad
 \widetilde M_U(s)=M_U(s)-a_Uv^{1-s},\quad
 \widetilde Y_U(s)=1-\zeta(s)\widetilde M_U(s).
 \tag{3.5}
\]
\(\widetilde M_U(1)=0\) точно. При \(\Re s>1\) абсолютная сходимость и (3.1) дают
\[
 \zeta(s)\widetilde M_U(s)
 =s\int_1^\infty\widetilde G_U(x)x^{-s-1}\,dx.
\]
По (3.4) интеграл аналитичен уже в \(\Re s>0\). Отделяя участок (3.3), получаем точное продолжение
\[
 \boxed{\widetilde Y_U(s)=
 v^{-s}-s\int_v^\infty\widetilde G_U(x)x^{-s-1}\,dx,
 \qquad\Re s>0.}
 \tag{3.6}
\]
Не предполагается сходимость исходного бесконечного ряда Мёбиуса слева от единицы. Это конечный полином, умноженный на \(\zeta\), и интеграл **его собственной** ограниченной примитивной функции.

Определим
\[
 b_U=\widetilde M_U'(1)=M_U'(1)+a_U\log v
 =\sum_{d\le U}\frac{\mu(d)}d\log(v/d),
 \qquad e_U=1-b_U=\widetilde Y_U(1).
 \tag{3.7}
\]
Из (3.6), без знакового предположения на хвост:
\[
 |e_U|\le\frac{1+Q_U+|\tau_U|}{v}=:\vartheta_U.
 \tag{3.8}
\]
Теперь используется дополнительная структура настоящей \(\mu\), отсутствующая у произвольных коэффициентных меток: \(\mu(d)=0\) для каждого \(4\mid d\). Поэтому
\[
 Q_U\le U-\lfloor U/4\rfloor.
\]
На cofinal множестве E1:
\[
 \vartheta_U\le
 1-\frac{\lfloor U/4\rfloor}{U+1}+\frac1{2U}
 \le\frac34+\frac1{U+1}+\frac1{2U}<\frac45
 \quad(U\ge64).
 \tag{3.9}
\]
Это доказывает (0.1), в частности \(1/5\le b_U\le9/5\).

**Это направленная количественная информация о настоящей связанной первой производной**, полученная из cofinal малости, точного floor-coupling и квадратсвободной поддержки. Она не получена из независимого назначения нижних моментов. Сильная оценка \(G(n,U)\) не использована.

### 3.3. Полная иерархия производных: равномерная область

**[COFINAL_FAMILY | PAPER]** Берём
\[
 r_U=\frac1{100\log v},\qquad |s-1|\le r_U.
\]
Здесь \(r_U<1/100\), \(\sigma=\Re s\ge1-r_U>0\). По (3.6)
\[
 |\widetilde Y_U(s)|
 \le v^{-\sigma}\left(1+\frac{|s|}{\sigma}S_U\right).
\]
Используем только явные константы:
\[
 v^{1-\sigma}\le e^{1/100}\le100/99,
 \qquad |s|/\sigma\le101/99.
\]
Вместе с (3.8)–(3.9):
\[
 \boxed{\sup_{|s-1|\le r_U}|\widetilde Y_U(s)|
 \le\frac{100}{99}\frac{101}{99}\frac45<\frac56.}
 \tag{3.10}
\]
Следовательно, для всех целых \(r\ge0\), с тем же \(U\),
\[
 \boxed{\left|\frac{d^r}{ds^r}\widetilde Y_U(s)^K\bigg|_{s=1}\right|
 \le r!(100\log v)^r(5/6)^K.}
 \tag{3.11}
\]
Это Cauchy на **явно заданном движущемся диске**, не перенос fixed-\(U\) асимптотики на растущий \(U\). Все смешанные произведения моментов входят в \(\widetilde Y_U^K\) до этой оценки.

Можно отдельно выписать контроль самих исходных моментов. Обозначим \(F(s)=(s-1)\zeta(s)\). Из элементарной формулы
\[
 \zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{x\}x^{-s-1}\,dx
 \qquad(\Re s>0)
\]
следует на указанном диске \(|F-1|\le2/99\), поэтому \(|F|\ge97/99>9/10\). Тогда
\[
 \frac{\widetilde M_U(s)}{s-1}
 =\frac{1-\widetilde Y_U(s)}{F(s)}
\]
аналитична и имеет модуль меньше \(3\). Ещё одна Cauchy-оценка даёт при \(r\ge1\)
\[
 \boxed{|M_U^{(r)}(1)-a_U(-\log v)^r|
 =|\widetilde M_U^{(r)}(1)|
 \le3r!(100\log v)^{r-1}.}
 \tag{3.12}
\]
Для \(r=1\) более сильна (0.1). Это uniform bound, а не утверждение о сходимости всех производных к производным \(1/\zeta\). В частности, здесь не утверждается \(M_U'(1)=1+O(U^{-c})\) или какой-либо Mertens-rate.

Формула для связи с нижними Laurent-комбинациями полностью явная: если \(N_U(s)=\widetilde M_U(s)/(s-1)\), то
\[
 \widetilde Y_U(s)=1-F(s)N_U(s),\qquad
 N_U^{(r)}(1)=\frac{\widetilde M_U^{(r+1)}(1)}{r+1}.
\]
Таким образом, (3.11) контролирует именно связанные комбинации всех нижних моментов, а не только \(a_U^K\).

---

## 4. Вся биномиальная сборка и точный конечный остаток

**[ABSTRACT | PAPER]** Единицу свёртки обозначаем \(\mathbf e=\delta_1\), постоянную арифметическую функцию — \(\mathbf1\). Положим
\[
 \widetilde y_U=\mathbf e-\mathbf1*\widetilde u_U.
\]
Поскольку (2.3) не меняет ни одного коэффициента до \(U\),
\[
 \widetilde y_U(n)=0\ (n\le U),\qquad
 \operatorname{supp}\widetilde y_U^{*K}\subseteq[v^K,\infty).
 \tag{4.1}
\]
Полная геометрическая формула конечной свёрточной алгебры, с фактическим обратным \(\mu\), даёт
\[
 \boxed{\Lambda=
 \sum_{j=1}^K(-1)^{j-1}\binom Kj
 \widetilde u_U^{*j}*\mathbf1^{*(j-1)}*\log
 +\Lambda*\widetilde y_U^{*K}.}
 \tag{4.2}
\]
Введём коэффициенты первой суммы \(\widetilde\lambda_{U,K}(n)\) и остатка \(r_{U,K}(n)\). На (2.2):
\[
 \boxed{\widetilde\lambda_{U,K}(n)=\Lambda(n),\quad
 r_{U,K}(n)=0\quad(1\le n\le m).}
 \tag{4.3}
\]
Ни \(\mu\), ни \(\Lambda\) в конечной цели не заменены. Вспомогательный атом в (2.3) может не совпадать с \(\mu(v)\); все порождённые им произведения в (4.2) сокращаются **совместно**. Отдельно объявлять их маленькими нельзя.

В частности, внутри \(\widetilde u_U^{*j}\) сохранено всё раскрытие
\[
 \widetilde u_U^{*j}=
 \sum_{h=0}^{j}\binom jh(-\tau_U)^h
 u_U^{*(j-h)}*\delta_{v^h}.
 \tag{4.4}
\]
Все переменные упорядочены, общий cutoff произведения буквальный. Пропуск смешанных \(0<h<j\) меняет источник. Если \(v^K\le m\), остаток (4.2) возвращается полностью, а не считается нулевым.

Для бесконечных Dirichlet-рядов на \(\Re s>1\), где всё абсолютно сходится:
\[
 D(s)=-\frac{\zeta'(s)}{\zeta(s)},
\]
\[
 \widetilde B_{U,K}(s)=D(s)[1-\widetilde Y_U(s)^K],\qquad
 \widetilde R_{U,K}(s)=D(s)\widetilde Y_U(s)^K,
 \qquad\widetilde B+\widetilde R=D.
 \tag{4.5}
\]
Это не новая гипотеза о контурном хвосте. Их коэффициенты — ровно (4.2).

### 4.1. Контроль исходного \(P\)

На прежнем физическом \(L^2(0,L)\):
\[
 (V_sf)(t)=\mathbf1_{s\le t\le L}f(t-s),\quad
 V_sV_t=V_{s+t},\quad V_s=0\ (s\ge L).
\]
Подстановка \(n^{-1/2}V_{\log n}\) в (4.2) законна до сжатия. После неё прибавляется adjoint и только затем применяются \(F_M,P\). Отдельные множители не обязаны сохранять \(P\), и это не используется.

Вся source-матрица после (4.2) равна прежней \(A_m\). **Новый projection-return равен нулю**, поскольку вектор и пространство вообще не меняются. Равенство сохраняет произвольные комплексные self/cross-члены одновременно для всех \(c=Pc\) и \(W=PWP\succeq0\), \(\operatorname{Tr}W=1\).

Индекс \(n=m\) сохраняется в коэффициентном равенстве. Его нулевой физический overlap не используется для удаления sinc-сглаженного верхнего атома в \(N_\star\). Если подставлять (4.2) в Q32, весь прежний \(r_\star\) начисляется **один раз**, не по каждому биномиальному каналу.

---

## 5. Полная искусственная полюсная иерархия оплачена

### 5.1. Почему не только старший полюс

**[ABSTRACT | PAPER]** Поскольку \(\widetilde M_U(1)=0\), \(\widetilde Y_U\) аналитична в единице. В (4.5) остаётся только простой полюс:
\[
 \boxed{\operatorname{Res}_{s=1}\widetilde B_{U,K}(s)
 =\kappa_U:=1-e_U^K,\qquad
 \operatorname{Res}_{s=1}\widetilde R_{U,K}(s)=e_U^K.}
 \tag{5.1}
\]
Все коэффициенты полюсов порядков \(2,\ldots,K+1\) равны нулю **точно**. Это следует из полной суммы, не из оплаты старшего коэффициента отдельно.

Для явной проверки положим \(t=s-1\), \(F=t\zeta\), \(N=\widetilde M_U/t\). Тогда
\[
 \widetilde B_{U,K}(1+t)=
 \frac{F-tF'}{t}
 \sum_{j=1}^{K}(-1)^{j-1}\binom Kj N^jF^{j-1}.
 \tag{5.2}
\]
Правая часть — аналитическая функция, делённая только на \(t\). В нуле её числитель равен \(1-(1-b_U)^K\). Не заменяем \(-\zeta'\) производной всего \(\zeta\widetilde M_U\): это добавило бы другую арифметику.

Из (3.9):
\[
 0<1-(4/5)^K\le\kappa_U\le1+(4/5)^K<2.
 \tag{5.3}
\]
Ни паритет \(K\), ни знак \(a_U\) не назначаются удобными. \(e_U\) вещественен, поэтому этот интервал верен для любого целого \(K\ge1\).

### 5.2. Uniform regular germ, но не бесплатная глобальная инверсия

Из той же элементарной интегральной формулы для \(\zeta\) на диске §3.3 следует \(|F'/F|<3\). Поэтому при \(|s-1|\le r_U/2\)
\[
 \boxed{
 \left|\widetilde B_{U,K}(s)-\frac{\kappa_U}{s-1}\right|
 \le\frac{2(5/6)^K}{r_U}+6.
 }
 \tag{5.4}
\]
Действительно, пишем \(D=1/(s-1)-F'/F\), а разность \(\widetilde Y_U(s)^K-e_U^K\) оплачиваем Cauchy по (3.10). Аналогичная оценка действует для \(\widetilde R-e_U^K/(s-1)\).

(5.4) **локальна**: диск сжимается как \(1/\log U\). Она не покрывает весь физический Fourier-диапазон, не даёт оценку всей вертикальной линии и не разрешает двигать общий контур с бесплатными горизонталями. В частности, маленькая \((5/6)^K\) при фиксированном \(\epsilon\) — константа, не степень по \(m\).

### 5.3. Возврат простого полюса с настоящим знаком

Обозначим причинный непрерывный оператор
\[
 \mathcal C_L=\int_0^L e^{s/2}V_s\,ds.
\]
Пара \(\mathcal C_L+\mathcal C_L^*\) имеет ядро \(e^{|t-u|/2}\). Два исходных экспоненциальных контакта и тождество
\[
 e^{|t-u|/2}=e^{(t-u)/2}+e^{(u-t)/2}-e^{-|t-u|/2}
\]
возвращают ровно
\[
 PF_M^*(\mathcal C_L+\mathcal C_L^*)F_MP=-H_d.
 \tag{5.5}
\]
Это известный continuous return из пакета, с проверенным здесь знаком и коэффициентом. Не новая теорема о CCM.

Следовательно, весь principal-part вклад (5.1) на исходном \(P\) равен
\[
 \boxed{-\kappa_UH_d\preceq0,\qquad
 \|\kappa_UH_d\|\le4[1+(4/5)^K].}
 \tag{5.6}
\]
Его верхняя плата — **ноль**. Малость одного \(a_U^K\) не использована как цена всей формы; возвращён весь исправленный полюсный блок.

---

## 6. Конечный остаток возвращён целиком, а не удалён по поддержке

### 6.1. Точное finite-window определение

Определим локально конечную signed-меру на причинной полуоси
\[
 d\mathfrak E_U(s)=
 \sum_{n\ge1}\frac{\widetilde\lambda_{U,K}(n)}{\sqrt n}\,
 \delta_{\log n}(ds)-\kappa_Ue^{s/2}\,ds.
 \tag{6.1}
\]
Её ограничение на \([0,L]\) определено без контурных пределов. По (4.3) дискретная часть в этом окне — **полная настоящая** \(\Lambda(n)/\sqrt n\). Никакое утверждение о далёком хвосте ряда не требуется для этого конечного определения.

Сжимая обе временные стороны, получаем
\[
 \boxed{
 A_m=-\kappa_UH_d+\mathcal F_{m,U},\qquad
 \mathcal F_{m,U}=C^0_m-e_U^K H_d.
 }
 \tag{6.2}
\]
Это точная полная signed-сборка, включая все нижние моменты, края, self/cross и prime powers. Поэтому
\[
 \boxed{-4(4/5)^KP\preceq\mathcal F_{m,U}-C^0_m
 \preceq4(4/5)^KP.}
 \tag{6.3}
\]
Цена изменения оставшейся матрицы — явная константа, но коэффициент самой \(C^0_m\) остаётся **один**.

### 6.2. Нулевая физическая поддержка \(\widetilde R\) не зануляет её полюс

Коэффициенты \(r_{U,K}\) дают нулевой причинный оператор в окне \([0,L]\), потому что \(v^K>m\). Но \(\widetilde R\) имеет residue \(e_U^K\). После вычитания этого простого полюса оставшаяся часть (регулярная лишь в \(s=1\), не объявленная целой всюду) на том же конечном окне равен \(-e_U^K\mathcal C_L\). Поэтому две сжатые части равны
\[
 -e_U^KH_d\quad\hbox{и}\quad+e_U^KH_d,
 \tag{6.4}
\]
и сокращаются в ноль **совместно**. Их нельзя удалить по отдельности.

Это можно формулировать вообще без нового контурного перехода: разность signed-мер и непрерывной экспоненты в Re\(s>1\) имеет указанный Laplace-transform, а её finite-window restriction вычислена непосредственно. Никакие неоценённые горизонтальные/вертикальные остатки не называются малыми.

В частности, возврат к \(B+R=D\) даёт
\[
 -\kappa_UH_d+\mathcal F_{m,U}
 =-H_d+C^0_m=A_m,
\]
с точным сокращением всей добавленной коррекции. В конечной арифметике не потеряно ни одного веса; небольшой вспомогательный атом не является лицензией на приближённое обращение.

### 6.3. Совместимость с уже оплаченным all-\(P\) контуром

S7 для **исходного** источника даёт
\[
 A_m=-H_d+\mathcal V_m-\mathcal R_m^{\rm sign}+\mathcal E_m,
 \qquad\|\mathcal V_m\|\le\mathfrak B_m,
 \quad\|\mathcal E_m\|\le\mathfrak e_m.
\]
Здесь общий для всего \(P\) контур и все его расходы остаются прежними. Просто подставляя точное (6.2), а не перенося оценки на другой бесконечный ряд, получаем
\[
 \boxed{\mathcal F_{m,U}=
 \mathcal V_m-\mathcal R_m^{\rm sign}+\mathcal E_m-e_U^KH_d.}
 \tag{6.5}
\]
В частности,
\[
 \mathcal F_{m,U}\preceq
 -\mathcal R_m^{\rm sign}
 +[\mathfrak B_m+\mathfrak e_m+4(4/5)^K]P.
\]
Все дополнительные аналитические расходы вписываются в прежние \(O_\epsilon(m^{2\epsilon})\). **Знак всей настоящей матрицы вычетов не изменён и не доказан.** Мы не пересчитываем adverse selected-zero identity и не используем его как благоприятный вход.

---

## 7. Первая неоплаченная строка и полный потребитель

Не доказан независимый upper
\[
 \boxed{\mathcal F_{m,U}\preceq
 D_\epsilon m^{\theta(\epsilon)}P,
 \qquad\theta(\epsilon)\longrightarrow0,}
 \tag{7.1 — UNPROVED}
\]
на одной общей неограниченной последовательности (2.2). Благодаря (6.3) это тот же signed debt \(C^0_m\), с точностью до полностью оплаченной константы. (7.1) не объявляется новой поставленной леммой и не принимается в предпосылки последующего «доказательства».

### 7.1. Почему проверенный первоисточник не закрывает эту строку

E1 supplies cofinal \(a_U\), а не необходимую количественную оценку всей \(G(n,U)\). В проверенной Theorem 3.1(14) такая оценка — условие. В нашей попытке независимо доказаны только (3.4), (3.8)–(3.12), которые дают локальные связанные моменты и favourable principal part. Ни один из этих результатов не контролирует полный signed pairing (6.1) с достижимой корреляцией для всех \(c=Pc\).

Дешёвая вспомогательная поправка не оправдывает бесплатную оценку \(Z^j\); запрет области из S3 не обходился. Локальная регулярность около \(s=1\) не является глобальной оценкой конечной физической матрицы. Неравномерная fixed-\(U\) асимптотика не использовалась.

### 7.2. Все платы

**[COFINAL_FAMILY | PAPER; new exact maps and inherited consumer estimates]**

| Элемент | Полная цена | Область |
|---|---|---|
| Один balancing-атом до сжатия | \(\le1/\sqrt{2U}\); его \(r\)-я \(\sigma\)-производная стоит ещё \((\log v)^r\) | Только этот атом, не произведение с \(Z^j\) |
| Полная mixed биномиальная смена источника через \(m\) | **0 точно** | (4.2)–(4.3), все коэффициенты |
| \(\Lambda*\widetilde y_U^{*K}\) в физическом окне | **0 точно** при \(v^K>m\) | Не удаляет его отдельный полюс; (6.4) возвращён |
| Artificial poles порядка \(\ge2\) | **0 точно** в полной repaired-сумме | Не утверждение о полюсах старых отдельных каналов |
| Полный простой pole block | \(-\kappa_UH_d\preceq0\); верхняя плата **0** | Все исходные комплексные \(P\)-векторы |
| \(\mathcal F_{m,U}-C^0_m\) | \(\le4(4/5)^K\) по норме | Полный остаток, не оценка \(C^0_m\) |
| Новый Fourier/contact-return | **0** | Вектор, окно, норма и \(P\) не меняются |
| Q32-return при работе через \(N_\star\) | Прежний \(r_\star\le C_\epsilon m^{2\epsilon}\), один раз | Не добавляется в прямой physical route повторно |
| Upper полной \(\mathcal F_{m,U}\) нужной степени | **Не доказан** | Первая неоплаченная строка (7.1) |

Если бы (7.1) было доказано, (5.6) и (6.2) дали бы \(A_m\preceq D_\epsilon m^{\theta(\epsilon)}P\), а затем
\[
 T_{>R}\preceq[D_\epsilon m^{\theta(\epsilon)}+b_{\rm div}]P,
\qquad
 PK_mP\succeq-[D_\epsilon m^{\theta(\epsilon)}+50L+8]P,
\]
\[
 b_{\rm div}=(56+32\Omega)\sqrt R+12(1+\log R)^2.
 \tag{7.2}
\]
Это только карта достаточности, не полученный бюджет.

**Полностью законное фактическое завершение.** По исходным оценкам:
\[
 A_m\preceq s_{\rm keep}P,
 \qquad s_{\rm keep}\le6\sqrt m+6m^{1/4}.
\]
Следовательно, без нового предположения
\[
 \mathcal F_{m,U}\preceq
 [s_{\rm keep}+4(1+(4/5)^K)]P.
 \tag{7.3}
\]
Это лишь унаследованный fallback, перенесённый в новую запись. Двусторонний безопасный верх \(\|\mathcal F_{m,U}\|\le12\sqrt m+4(1+(4/5)^K)\) также следует из прежнего prime-norm, но не используется как новый механизм.

Нет смысла добавлять цену (7.3) к исходной оценке, которая уже известна непосредственно. Поэтому окончательно сохраняем
\[
 \boxed{T_{>R}\preceq[s_{\rm keep}+b_{\rm div}]P,\qquad
 PK_mP\succeq-[s_{\rm keep}+50L+8]P.}
 \tag{7.4}
\]
Короткая делительная плата возникает один раз только для \(T_{>R}\); нет повторных \(H_d\), prime-power, \(U_{\rm sf}\) или Q32-плат в прямой \(K\)-оценке. Все \(\Lambda(p^j)\) уже находятся в исходном \(A_m\). По (7.4) полная безусловная степень остаётся \(1/2\). Условный \(3/8\) остаётся условным на прежнюю ZF78; она не использована в Q42.

---

## 8. Выполненный rollback и граница полезности

В отличие от оплаты одного старшего полюса, здесь проверена вся cofinal-иерархия, а её полюсный блок действительно перестал быть большим. Но (6.2) показывает, что **продолжать выбор \(U\) только ради меньшего pole coefficient не обосновано**. Полная remaining source-матрица отличается от прежнего центра лишь ограниченной матрицей.

Выполненный ранний возврат:
\[
 C^0_m=\mathcal F_{m,U}+e_U^KH_d
       =N_\star+E_\star+H_d.
 \tag{8.1}
\]
Первая карта точная; у второй сохраняется ровно один ранее оплаченный \(E_\star\). Никакой новой source replacement, промежуточной проекции или произвольного момента нет.

Две документированные записи остаются открытыми, не как новые запросы:

| Представление | Полная цена карты | Что может изменить математический вывод | Решающий эффект / стоимость |
|---|---|---|---|
| Прямое \(C^0_m\) на исходном \(P\) | Точная карта; \(0\preceq H_d\preceq4P\) | Независимое неравенство для всей signed-меры и её достижимой корреляции | При успехе непосредственно идёт в consumer; новая аналитическая цена отсутствует, арифметический шаг открыт |
| Полное \(N_\star\) из Q32 | \(O_\epsilon(m^{2\epsilon})\) один раз | Совместный source/test upper до разделения Fourier-полинома и матрицы | При успехе показатель \(\max(\theta,2\epsilon)\); карта известна, новый signed-вход не найден |

**DISCRIMINATOR.** Для следующего предлагаемого входа требуется проверить весь \(\mathfrak E_U\) / \(C^0_m\), не только его germ у \(s=1\). У нулевого физического remainder может оставаться ненулевой отдельный residue (6.4). А на настоящих больших простых полный конечный коэффициент остаётся \(\log p\). Кандидат обязан сохранить оба факта и произвольные поляризованные complex terms.

Самое сильное возражение: «Получены хорошие моменты, но новая матрица в (6.2) опять содержит исходную цель». **Да.** Поэтому статус основного потребителя `NO_PROGRESS`. Новая вспомогательная лемма не заявляется закрытием RH, SP, G1/G3 или уменьшением полного арифметического показателя.

Никакая theorem-shape не объявлена невозможной. В частности, мы не доказали, что \(a_U\) и остальные настоящие данные никогда не смогут дать сильное совместное сравнение. Доказано только то, что выполненный перенос поставил положительный principal coefficient и полную uniform moment estimate, но не нужный знак finite remainder.

---

## 9. Проверки, регистрация и эпистемические границы

Новые проверки написаны только для чувствительных мест расчёта. Старый код из S2 не запускался.

- Конечная actual-\(\mu\) реконструкция проверяется с рациональным balancing-коэффициентом, полными формальными координатами \(\log p\), всеми powers и верхним индексом. Есть как support-valid, так и nonzero-remainder режим.
- Проверены полы на целых и нецелых швах, точное равенство полного первого момента нулю и сохранение префикса.
- Для трёх настоящих \(U\ge64\), выбранных только по точному условию \(U|a_U|\le1/2\), вычислены рациональные внешние интервалы \(b_U\). Логарифмы ограждены сходящимся atanh-рядом с явным хвостом. Это не float-знак и не Arb.
- Generic rational germ controls проверяют именно алгебру отсутствия higher poles; они не являются моделью actual \(\mu\) или spectrum-тестом.
- Семь намеренных ошибок обнаружены: неверный знак коррекции; перенос коррекции внутрь сохранённого префикса; потеря mixed powers; замена \(\mu\) на \(|\mu|\); удаление ненулевого конечного остатка; зануление residue по поддержке; неверный знак continuum-return.

В actual moment-панели получены, например,
\[
 b_{67}\in[1.00126191,1.00126192],\quad
 b_{247}\in[1.00051732,1.00051733],\quad
 b_{430}\in[1.00066867,1.00066868].
\]
Эти десятичные интервалы — точные рациональные endpoints из результата, не округлённый float-критерий. Универсальные (3.9)–(3.12) доказываются выше, **не экстраполируются** из этой панели. В этих тестах не вычислялась производственная CCM-матрица при астрономических \(m\) из (2.2).

Пререгистрация создана после чтения и бумажного выбора конструкции, но до новых executable controls. Это не задним числом зарегистрированный прогноз всей аналитической работы.

| Предсказание | Судьба |
|---|---|
| P1: balancing сохраняет префикс и полную конечную \(\Lambda\) | Подтверждено доказательством и exact controls |
| P2: у полной repaired-суммы только простой residue \(1-(1-b_U)^K\) | Подтверждено полной формулой и germ controls |
| P3: на указанном cofinal множестве \(|1-b_U|\le4/5\) | Доказано uniform оценкой; панель только проверяет чувствительные знаки |
| P4: finite return не следует из local germ, возвращается \(C^0\) с коэффициентом один | Подтверждено (6.2)–(6.5), не объявлено no-go |

Исполнялись только включённые ниже новые стандартно-библиотечные проверяющие. Результаты после извлечения из окончательного Markdown повторно воспроизводятся побайтно. Не выполнялись новые независимый математический аудит, Lean, Arb, spectrum-расчёт, установки, запись в репозиторий или отправка нового запроса.

---

## 10. Dependency epistemics и closeout

```yaml
DOWNSTREAM_CONSUMER: ORIGINAL_T_GT_R_UPPER_AND_SPARSE_CCM_RECEIVER
ACTUAL_CONSUMER_REQUIREMENT: >-
  For each fixed sufficiently small epsilon, an upper on the same original P
  with eta(epsilon)->0 and complete returns; a common unbounded m subsequence
  is admissible under the inherited eventual negative-witness receiver.
ORIGINAL_REQUESTED_OBJECT: JOINT_COFINAL_SHORT_MOBIUS_SIGNED_BOUND
ORIGINAL_OBJECT_IS: NOT_NECESSARY
ORIGINAL_OBJECT_NOTE: >-
  Short-inverse pole control is a chosen sufficient route component, not a
  proved necessary condition for RH or for the unchanged CCM consumer.
KNOWN_WEAKER_INTERFACES: >-
  The accepted actual-source pair receiver is weaker than an all-P upper,
  but no independent favorable pair margin is supplied in Q42.
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: >-
  Uniform actual cofinal lower-moment combinations and a full mass-balanced
  finite return; no global-novelty claim and no new consumer exponent.
REOPEN_TRIGGER: >-
  A source-dependent one-sided estimate for the complete finite remainder,
  with the actual mixed weights and hyperbolic cutoff. Local germ bounds
  or the conditional G(n,U) hypothesis alone do not meet this trigger.
KILL_SCOPE: NONE
MATHEMATICALLY_DEAD: NONE
CLOSES: []
OPENS: []
```

**Что стало меньше?** Вспомогательный artificial-pole bookkeeping: вся иерархия снята с uniform lower-moment контролем и нулевой finite-map ошибкой. Основной signed arithmetic debt не уменьшился.

**Что не повторять?** Оплату только \(a_U^K\), бесплатное повторение constrained \(Z\), удаление residue по нулевой causal support, перенос локальной \(s=1\)-оценки на всю инверсию, объявление (14) известной теоремой.

**Одно действие для независимого проверяющего, без диспетчеризации нового запроса:** проверить (3.6)–(3.12), сохранение всех mixed terms в (4.2), коэффициент и знак (5.6), и точный finite-window return (6.2)–(6.5). Проверка должна оставить (7.1) открытой; никаких source-state продвижений не предлагается.

```yaml
iteration: Q42
status: NO_PROGRESS
auxiliary_status: PAPER_DERIVATION_WITH_EXACT_LOCAL_CONTROLS
failed_completion: LOCAL_COFINAL_MOMENTS_DO_NOT_SUPPLY_FULL_FINITE_SIGN
cognitive_operator_used: REPRESENTATION_SHIFT
new_gap_name: NONE_ORIGINAL_SIGNED_CORE_RETAINED
invariant_learned: >-
  All artificial poles can be removed by an explicit balanced short inverse
  without changing any finite source coefficient; the remaining form still
  contains the original centered arithmetic with coefficient one.
forbidden_future_move: >-
  Treating a favorable artificial principal part as a bound for the whole source.
next_decisive_test: READ_ONLY_AUDIT_OF_UNIFORM_MOMENT_AND_FINITE_RETURN_LEMMA
route_score_primary: 2
RH_CLAIM: NOT_MADE
```

## 11. Полный manifest входов

Строки следующей таблицы относятся к каноническому TXT. Размеры — точные UTF-8 bytes; внешний separator LF не входит в body.

| ID | Имя | Bytes | LF | Строки TXT | SHA-256 |
|---|---|---:|---:|---|---|
| S1 | `CCM_Q41_CONCLUSION.md` | 3266 | 60 | 30–89 | `97e433130c802dcb798d2630d4c15f7a28dc835d79e785efbf32e01cb1e7901e` |
| S2 | `PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_VERDICT_2026-10-26.md` | 67429 | 1214 | 94–1307 | `db0b177c2494f1fa1376f2c058860f8ec38561f92d5bb6c8ccdec5f8c068335c` |
| S3 | `CCM_POST_Q41_SECOND_INVERSE_PREFLIGHT.md` | 4867 | 89 | 1312–1400 | `b64182ee4982887c85bb76bb24bcf566d8465c3841347b061e5915a0602c9dcc` |
| S4 | `CCM_POST_Q41_JOINT_MOBIUS_POLE_PREFLIGHT.md` | 3989 | 74 | 1405–1478 | `883e3f982b74794d863558243ed922f0e33880d3c0fffa3e49d4a3d222d1b782` |
| S5 | `CCM_POST_Q41_COFINAL_MOBIUS_MOMENT.md` | 3719 | 66 | 1483–1548 | `ff75e7c78c8a4448ba21a0d7961bca950ac8aae4db55c7cb928f3df7118fd8aa` |
| S6 | `CCM_JOINT_Q04_CONCLUSION.md` | 5036 | 92 | 1553–1644 | `617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086` |
| S7 | `CCM_POST_Q27_ORIGINAL_P_CONTOUR.md` | 5633 | 123 | 1649–1771 | `109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2` |
| S8 | `CCM_Q32_CONCLUSION.md` | 3625 | 64 | 1776–1839 | `183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245` |
| S9 | `CCM_SPARSE_BAND_RECEIVER.md` | 6174 | 69 | 1844–1912 | `0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06` |
| S10 | `CCM_Q40_CONCLUSION.md` | 5988 | 111 | 1917–2027 | `e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06` |

## 12. Воспроизведение встроенных приложений

Сохрани этот Markdown рядом с каноническим TXT. Команда ниже извлекает только шесть **новых** приложений Q42, проверяет их хеши, запускает два проверяющих и сравнивает результаты побайтно. Исторические scripts из source bodies не исполняются. Нужен обычный Python 3 со стандартной библиотекой; установки не требуются.

```bash
python3 - \
  PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_VERDICT_2026-10-26.md \
  PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_2026-10-26.txt \
  q42_replay <<'PY'
from pathlib import Path
import hashlib, json, re, subprocess, sys
md, packet, out = Path(sys.argv[1]), Path(sys.argv[2]).resolve(), Path(sys.argv[3]).resolve()
data = md.read_bytes(); out.mkdir(parents=True, exist_ok=True)
pat = re.compile(rb'^BEGIN_Q42_ASSET ([A-Za-z0-9_.-]+) BYTES=(\d+) SHA256=([0-9a-f]{64})\n```[^\n]*\n', re.M)
assets = {}
for hit in pat.finditer(data):
    name = hit[1].decode(); start = hit.end(); size = int(hit[2])
    body = data[start:start+size]
    if name in assets or len(body) != size or hashlib.sha256(body).hexdigest() != hit[3].decode():
        raise ValueError('Asset mismatch: ' + name)
    if data[start+size:start+size+4] != b'```\n':
        raise ValueError('Closing fence mismatch: ' + name)
    assets[name] = body; (out/name).write_bytes(body)
expected = {'preregistration.json','q42_source_manifest.json','check_q42.py',
            'q42_math_results.json','verify_q42_sources.py','q42_source_verification.json'}
if set(assets) != expected: raise ValueError('Unexpected asset set')
for script,args in [('check_q42.py',[]),('verify_q42_sources.py',[str(packet)])]:
    run = subprocess.run([sys.executable,str(out/script),*args],cwd=out,
                         check=True,capture_output=True,text=True)
    (out/(script+'.stdout')).write_text(run.stdout,encoding='utf-8')
for name in ('q42_math_results.json','q42_source_verification.json'):
    if (out/name).read_bytes() != assets[name]: raise ValueError('Replay differs: '+name)
print(json.dumps({'assets':len(assets),'checkers_run':2,'json_byte_identical':True,
                  'historical_scripts_run':False},sort_keys=True,indent=2))
PY
```

Первые два аргумента — пути к реально сохранённым Markdown и TXT. Третий — новый каталог результата. Например, при сохранении в Downloads замени первый аргумент на `"$HOME/Downloads/PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_VERDICT_2026-10-26.md"`; аналогично замени путь ко второму файлу.

### `preregistration.json`

BEGIN_Q42_ASSET preregistration.json BYTES=1147 SHA256=3003b1d41825be5a1008f31cd313632772333ffb5ecdfcc00cdd52c0ceba84f3
```json
{
  "chosen_mechanism": "Cofinal mass-balanced short inverse at first unused index v=U+1, complete binomial recombination before compression; all artificial poles and finite return retained.",
  "not_predicted": [
    "A new all-P CCM upper",
    "RH",
    "Theorem3.1(14) of Gallardo-Gutierrez/Seco"
  ],
  "predictions": {
    "P1": "Mass balancing leaves the first U coefficients unchanged and the exact Lambda reconstruction through m when (U+1)^K>m.",
    "P2": "The complete repaired germ has no pole of order >=2; its simple residue is 1-(1-b_U)^K.",
    "P3": "Using actual Mobius divisor identity and squarefree support yields |1-b_U|<=4/5 for U>=64 with U|a_U|<=1/2.",
    "P4": "The finite signed remainder is not controlled by the local pole bound; its exact return restores C0 with coefficient one."
  },
  "request_id": "Q42_COFINAL_SHORT_MOBIUS_JOINT",
  "stage": "After source reading and paper design; before new executable mathematical controls. Not a preregistration of completed derivations.",
  "tests_scope": "Finite algebra, exact rational arithmetic, and generic germ bookkeeping only; paper proof supplies quantifiers."
}
```
END_Q42_ASSET

### `q42_source_manifest.json`

BEGIN_Q42_ASSET q42_source_manifest.json BYTES=2731 SHA256=883189c24dcd6a64ada872d72d21bdef362303b9c475691d89b924e6485dbddd
```json
{
  "bytes": 117726,
  "file": "PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_2026-10-26.txt",
  "lf": 2030,
  "sha256": "d4ce7e99338317abb4382a00f0baaa5e6808221eb71543360b94b76535d444d6",
  "sources": [
    {
      "bytes": 3266,
      "end_line": 89,
      "id": "S1",
      "lf": 60,
      "name": "CCM_Q41_CONCLUSION.md",
      "sha256": "97e433130c802dcb798d2630d4c15f7a28dc835d79e785efbf32e01cb1e7901e",
      "start_line": 30
    },
    {
      "bytes": 67429,
      "end_line": 1307,
      "id": "S2",
      "lf": 1214,
      "name": "PROSHKA_CCM_EARLIER_FORK_SIGNED_SOURCE_Q41_VERDICT_2026-10-26.md",
      "sha256": "db0b177c2494f1fa1376f2c058860f8ec38561f92d5bb6c8ccdec5f8c068335c",
      "start_line": 94
    },
    {
      "bytes": 4867,
      "end_line": 1400,
      "id": "S3",
      "lf": 89,
      "name": "CCM_POST_Q41_SECOND_INVERSE_PREFLIGHT.md",
      "sha256": "b64182ee4982887c85bb76bb24bcf566d8465c3841347b061e5915a0602c9dcc",
      "start_line": 1312
    },
    {
      "bytes": 3989,
      "end_line": 1478,
      "id": "S4",
      "lf": 74,
      "name": "CCM_POST_Q41_JOINT_MOBIUS_POLE_PREFLIGHT.md",
      "sha256": "883e3f982b74794d863558243ed922f0e33880d3c0fffa3e49d4a3d222d1b782",
      "start_line": 1405
    },
    {
      "bytes": 3719,
      "end_line": 1548,
      "id": "S5",
      "lf": 66,
      "name": "CCM_POST_Q41_COFINAL_MOBIUS_MOMENT.md",
      "sha256": "ff75e7c78c8a4448ba21a0d7961bca950ac8aae4db55c7cb928f3df7118fd8aa",
      "start_line": 1483
    },
    {
      "bytes": 5036,
      "end_line": 1644,
      "id": "S6",
      "lf": 92,
      "name": "CCM_JOINT_Q04_CONCLUSION.md",
      "sha256": "617876f6f9a83d8fb4c32b53864968534aaa950b670fa3e83f06da6fd2e61086",
      "start_line": 1553
    },
    {
      "bytes": 5633,
      "end_line": 1771,
      "id": "S7",
      "lf": 123,
      "name": "CCM_POST_Q27_ORIGINAL_P_CONTOUR.md",
      "sha256": "109c8ce6d357281eacca4697f1373f165befcbc62926b9c7254545e63d66d3b2",
      "start_line": 1649
    },
    {
      "bytes": 3625,
      "end_line": 1839,
      "id": "S8",
      "lf": 64,
      "name": "CCM_Q32_CONCLUSION.md",
      "sha256": "183d938014b47b8ac21e83ee13e5e605908f27f1198011a26513b365ed127245",
      "start_line": 1776
    },
    {
      "bytes": 6174,
      "end_line": 1912,
      "id": "S9",
      "lf": 69,
      "name": "CCM_SPARSE_BAND_RECEIVER.md",
      "sha256": "0effe9636da2d4898f78ab97c4932016c484ef60e6ed0e1be296e0a7d2b18d06",
      "start_line": 1844
    },
    {
      "bytes": 5988,
      "end_line": 2027,
      "id": "S10",
      "lf": 111,
      "name": "CCM_Q40_CONCLUSION.md",
      "sha256": "e77ad2f2014b46a54d60f2ad4f9eadff172f8ae6c9a91ba2c03a59a9c2a6ea06",
      "start_line": 1917
    }
  ]
}
```
END_Q42_ASSET

### `check_q42.py`

BEGIN_Q42_ASSET check_q42.py BYTES=8846 SHA256=3ccc85c8bfda755ec5f5288e396750e238a1483f0baa8b5390c0a9142c649374
```python
#!/usr/bin/env python3
"""Exact algebra/interval diagnostics, not a CCM spectral certificate. Stdlib only."""
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
import json


def factors(n):
    out = {}; d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0)+1; n //= d
        d += 1
    if n > 1: out[n] = out.get(n, 0)+1
    return out


def mu(n):
    d = factors(n)
    return 0 if any(v>1 for v in d.values()) else (-1)**len(d)


def conv(a, b):
    if len(a) != len(b): raise ValueError('different carriers')
    m = len(a)-1; c = [F(0) for _ in a]
    for d in range(1,m+1):
        if a[d]:
            for k in range(1,m//d+1):
                if b[k]: c[d*k] += a[d]*b[k]
    return c


def power(a, j):
    out = [F(0) for _ in a]; out[1] = F(1)
    for _ in range(j): out = conv(out,a)
    return out


def make_inverse(m, U, *, sign=-1, place=None, absolute=False):
    if m < U+1: raise ValueError('need full repair atom')
    v = U+1 if place is None else place
    a = sum((F(mu(d),d) for d in range(1,U+1)),F())
    u = [F(0)]*(m+1)
    for d in range(1,U+1): u[d] = F(abs(mu(d)) if absolute else mu(d))
    u[v] += sign*v*a
    return u,a,v


def expansion(u, K, drop_mixed_base=None):
    m=len(u)-1; one=[F(0)]+[F(1)]*m
    unit=[F(0)]*(m+1); unit[1]=1
    y=[unit[n]-z for n,z in enumerate(conv(one,u))]
    total=[F(0)]*(m+1)
    for j in range(1,K+1):
        uj=power(u,j)
        if drop_mixed_base is not None:
            d=[x-z for x,z in zip(u,drop_mixed_base)]
            uj=[x+z for x,z in zip(power(drop_mixed_base,j),power(d,j))]
        row=conv(uj,power(one,j-1)); c=(-1)**(j-1)*comb(K,j)
        total=[x+c*z for x,z in zip(total,row)]
    return total,y,power(y,K)


def log_coords(m):
    fs=[{}]+[factors(n) for n in range(1,m+1)]
    for p in range(2,m+1):
        if fs[p] != {p:1}: continue
        ell=[F(0)]+[F(fs[n].get(p,0)) for n in range(1,m+1)]
        lam=[F(0)]+[F(int(len(fs[n])==1 and p in fs[n])) for n in range(1,m+1)]
        yield p,ell,lam


def log_unit_interval(q, terms=24):
    """Rational outward bounds for log(q), 1<=q<=2."""
    assert F(1)<=q<=F(2)
    t=(q-1)/(q+1)
    lo=2*sum((t**(2*j+1)/F(2*j+1) for j in range(terms)),F())
    rem=2*t**(2*terms+1)/(F(2*terms+1)*(1-t*t))
    return lo,lo+rem


def log_ratio(q):
    assert q>=1
    k=0
    while q>2: q/=2; k+=1
    a,b=log_unit_interval(q); c,d=log_unit_interval(F(2))
    return a+k*c,b+k*d


def moment_interval(U):
    lo=hi=F(0); v=U+1
    for d in range(1,U+1):
        z=F(mu(d),d)
        if not z: continue
        a,b=log_ratio(F(v,d))
        if z>0: lo+=z*a; hi+=z*b
        else: lo+=z*b; hi+=z*a
    return lo,hi


def poly_add(a,b):
    c={k:a.get(k,F())+b.get(k,F()) for k in a.keys()|b.keys()}
    return {k:v for k,v in c.items() if v}


def poly_mul(a,b):
    c={}
    for k,v in a.items():
        for l,w in b.items(): c[k+l]=c.get(k+l,F())+v*w
    return {k:v for k,v in c.items() if v}


def poly_power(a,j):
    c={0:F(1)}
    for _ in range(j): c=poly_mul(c,a)
    return c


def scale(a,t): return {k:t*v for k,v in a.items() if t*v}


def shift(a,j): return {k+j:v for k,v in a.items()}


def run():
    verified=[]; planted={}
    for m,U,K in [(32,2,4),(127,5,3),(215,5,3),(300,7,3)]:
        u,a,v=make_inverse(m,U)
        total,y,yk=expansion(u,K)
        assert all(y[n]==0 for n in range(1,U+1))
        assert sum((u[d]/d for d in range(1,m+1)),F())==0
        assert v**K>m and not any(yk)
        assert total==[F(0)]+[F(mu(n)) for n in range(1,m+1)]
        for p,ell,lam in log_coords(m): assert conv(total,ell)==lam
        verified.append({'m':m,'U':U,'K':K,'a_U':str(a),'repair':str(-v*a)})
    # A genuinely nonzero finite remainder, retaining formal prime-power logs.
    m,U,K=80,2,2
    u,a,v=make_inverse(m,U); total,y,yk=expansion(u,K)
    remainder_nonzero=False
    for p,ell,lam in log_coords(m):
        remainder=conv(lam,yk); recovered=conv(total,ell)
        assert [x+z for x,z in zip(recovered,remainder)]==lam
        remainder_nonzero |= any(remainder)
        if p==2: assert remainder[18]==F(1,4)
    assert remainder_nonzero
    planted['delete_nonzero_hyperbolic_remainder']=remainder_nonzero
    # Primitive, real-floor seams, not integer samples alone.
    for U in [2,5,7,11]:
        m=4*(U+1); u,a,v=make_inverse(m,U)
        S=sum(abs(z) for z in u)
        for j in range(3,12*v+1):
            x=F(j,3)
            G=sum((u[d]*(x//d) for d in range(1,m+1)),F())
            frac=-sum((u[d]*(x/d-(x//d)) for d in range(1,m+1)),F())
            assert G==frac and abs(G)<=S
            if x<v: assert G==1
    # Select a small source panel by the exact cofinal predicate only.
    candidates=[]; a=F()
    for U in range(1,513):
        a+=F(mu(U),U)
        if U>=64 and U*abs(a)<=F(1,2): candidates.append((U,a))
    assert candidates
    chosen=[candidates[i] for i in sorted({0,len(candidates)//2,len(candidates)-1})]
    panel=[]
    for U,a in chosen:
        v=U+1; Q=sum(mu(d)**2 for d in range(1,U+1))
        theta=(1+F(Q)+v*abs(a))/v
        assert theta<=F(4,5)
        lo,hi=moment_interval(U)
        assert lo>=1-theta and hi<=1+theta
        # Compact decimal-free enclosure for reporting.
        sc=10**8
        lo8=F((lo*sc).__floor__(),sc); hi8=F((hi*sc).__ceil__(),sc)
        panel.append({'U':U,'a_U':str(a),'theta_U':str(theta),
                      'b_U_lower':str(lo8),'b_U_upper':str(hi8)})
    assert F(100,99)*F(101,99)*F(4,5)<F(5,6)
    # Uniform scalar threshold for all U>=64: use decreasing envelope, not a panel extrapolation.
    assert F(3,4)+F(1,65)+F(1,128)<F(4,5)
    # Joint local germs: -zeta' * sum binomial M^j zeta^(j-1).
    germ_cases=[]
    for K,b in [(2,F(1,3)),(3,F(7,5)),(4,F(9,10))]:
        Z={-1:F(1),0:F(2,5),1:F(-1,7),2:F(1,11)}
        MT={1:b,2:F(-2,9),3:F(1,13)}
        negder={k-1:-k*v for k,v in Z.items() if k}
        B={}
        for j in range(1,K+1):
            row=poly_mul(poly_power(MT,j),poly_power(Z,j-1))
            B=poly_add(B,scale(poly_mul(negder,row),F((-1)**(j-1)*comb(K,j))))
        assert min(B)>=-1 and B.get(-1,F())==1-(1-b)**K
        # Before repair, the highest pole survives.
        a=F(-1,30); M0=poly_add(MT,{0:a}); old={}
        for j in range(1,K+1):
            row=poly_mul(poly_power(M0,j),poly_power(Z,j-1))
            old=poly_add(old,scale(poly_mul(negder,row),F((-1)**(j-1)*comb(K,j))))
        assert old[-K-1]==(-1)**(K+1)*a**K
        germ_cases.append({'K':K,'b':str(b),'simple_residue':str(B[-1])})
    # Sensitive failures.
    bad,a,v=make_inverse(80,5,sign=1)
    planted['wrong_balancing_sign']=sum((bad[d]/d for d in range(1,81)),F())!=0
    bad,a,v=make_inverse(80,5,place=5)
    _,y,_=expansion(bad,3)
    planted['repair_inside_preserved_prefix']=any(y[n] for n in range(1,6))
    u,a,v=make_inverse(80,5); base=[F(0)]+[F(mu(n) if n<=5 else 0) for n in range(1,81)]
    wrong,_,_=expansion(u,3,drop_mixed_base=base)
    planted['drop_repair_mixed_products']=wrong!=[F(0)]+[F(mu(n)) for n in range(1,81)]
    bad,a,v=make_inverse(80,5,absolute=True)
    wrong,_,_=expansion(bad,3)
    planted['replace_actual_mu_by_moduli']=wrong!=[F(0)]+[F(mu(n)) for n in range(1,81)]
    # A zero-support remainder can still have nonzero simple-pole germ.
    alo,ahi=moment_interval(chosen[0][0])
    assert alo>1 or ahi<1  # actual cofinal moment: e_U is rigorously nonzero
    planted['discard_remainder_residue_from_support']=(alo>1 or ahi<1)
    # Exact return: E = C0 - e^K H and A = E - (1-e^K)H.
    C,H,e,K=F(7,3),F(5,7),F(-1,3),3
    E=C-e**K*H; A=C-H
    assert E-(1-e**K)*H==A
    planted['wrong_continuum_return_sign']=E+(1-e**K)*H!=A
    assert all(planted.values())
    # Cofinal schedule without floating-point fractional powers.
    for U in (5,64,100):
        m=U**33; assert (U+1)**33>m
        x=U**65; m=isqrt(x)
        if m*m<x: m+=1
        assert U**65<=m*m<(U+1)**65 and (U+1)**33>m
    return {'status':'EXACT_AUXILIARY_ALGEBRA_AND_MOMENT_CONTROLS_ONLY',
            'finite_reconstruction_cases':verified,'nonzero_remainder_case':{'m':80,'U':2,'K':2,'log2_coefficient_at18':'1/4'},
            'actual_mobius_moment_intervals':panel,'generic_germ_cases':germ_cases,
            'primitive_floor_controls':'passed at integer and noninteger seams',
            'cofinal_schedule_integer_controls':'passed',
            'planted_failures_detected':planted,'planted_failure_count':len(planted),
            'source_quantifiers_supplied_by':'paper derivation, not the finite panel',
            'production_spectrum':False,'lean':False,'arb':False,'rh_claim':False}


if __name__=='__main__':
    obj=run(); text=json.dumps(obj,sort_keys=True,indent=2)+'\n'
    Path(__file__).with_name('q42_math_results.json').write_text(text)
    print(text,end='')
```
END_Q42_ASSET

### `q42_math_results.json`

BEGIN_Q42_ASSET q42_math_results.json BYTES=3203 SHA256=7c1e5e514f52e2ad34a5a884cdb54d8ab6ceb1f89891e8c448319f853d690d49
```json
{
  "actual_mobius_moment_intervals": [
    {
      "U": 67,
      "a_U": "1690811146852662245882/1309720258513377842646515",
      "b_U_lower": "100126191/100000000",
      "b_U_upper": "6257887/6250000",
      "theta_U": "3319585074944778133324713/5238881034053511370586060"
    },
    {
      "U": 247,
      "a_U": "46940068675143310336210174628247248858323029323195816342493536373528855191064969130473185757471/85347053011830869684370033503461770665179530666147686738704858805973639266773842168028155037495910",
      "b_U_lower": "25012933/25000000",
      "b_U_upper": "100051733/100000000",
      "theta_U": "210802262061960622623741858860281552088537617793431429572173899908622612321028741355688146303302049/341388212047323478737480134013847082660718122664590746954819435223894557067095368672112620149983640"
    },
    {
      "U": 430,
      "a_U": "956071782713231570678755370763051340736336440483436467509084334016898598777877639379994355121533650665792717575522020377833502858807365279317708386253821294432539880784/1471313432701246949165642271151785975544176322028704081991120917295380747276377897540670473785277738361782416471893111491492435042998373939636152172429741579163280492944695",
      "b_U_lower": "100066867/100000000",
      "b_U_upper": "25016717/25000000",
      "theta_U": "387367499738777350437526460877718586695975733699397534681161216596646419829760652315769112172585426192585732193382938313045356656040718320559693953663497432297843194333072689/634136089494237435090391818866419755459539994794371459338173115354309102076118873840028974201454705233928221499385931052833239503532299167983181586317218620619373892459163545"
    }
  ],
  "arb": false,
  "cofinal_schedule_integer_controls": "passed",
  "finite_reconstruction_cases": [
    {
      "K": 4,
      "U": 2,
      "a_U": "1/2",
      "m": 32,
      "repair": "-3/2"
    },
    {
      "K": 3,
      "U": 5,
      "a_U": "-1/30",
      "m": 127,
      "repair": "1/5"
    },
    {
      "K": 3,
      "U": 5,
      "a_U": "-1/30",
      "m": 215,
      "repair": "1/5"
    },
    {
      "K": 3,
      "U": 7,
      "a_U": "-1/105",
      "m": 300,
      "repair": "8/105"
    }
  ],
  "generic_germ_cases": [
    {
      "K": 2,
      "b": "1/3",
      "simple_residue": "5/9"
    },
    {
      "K": 3,
      "b": "7/5",
      "simple_residue": "133/125"
    },
    {
      "K": 4,
      "b": "9/10",
      "simple_residue": "9999/10000"
    }
  ],
  "lean": false,
  "nonzero_remainder_case": {
    "K": 2,
    "U": 2,
    "log2_coefficient_at18": "1/4",
    "m": 80
  },
  "planted_failure_count": 7,
  "planted_failures_detected": {
    "delete_nonzero_hyperbolic_remainder": true,
    "discard_remainder_residue_from_support": true,
    "drop_repair_mixed_products": true,
    "repair_inside_preserved_prefix": true,
    "replace_actual_mu_by_moduli": true,
    "wrong_balancing_sign": true,
    "wrong_continuum_return_sign": true
  },
  "primitive_floor_controls": "passed at integer and noninteger seams",
  "production_spectrum": false,
  "rh_claim": false,
  "source_quantifiers_supplied_by": "paper derivation, not the finite panel",
  "status": "EXACT_AUXILIARY_ALGEBRA_AND_MOMENT_CONTROLS_ONLY"
}
```
END_Q42_ASSET

### `verify_q42_sources.py`

BEGIN_Q42_ASSET verify_q42_sources.py BYTES=2431 SHA256=ae45ab77eb2db47bf0a8134183983948e7ac43b32347db558bb521cfb2acc6d2
```python
#!/usr/bin/env python3
"""Byte-framed Q42 intake verification. Never executes historical source code."""
import argparse, hashlib, json, re
from pathlib import Path

HEADER=re.compile(rb'BEGIN_SOURCE (S\d+) (\S+) BYTES=(\d+) LF=(\d+) SHA256=([0-9a-f]{64})\n')

def inspect(data, expected):
    data.decode('utf-8',errors='strict')
    sha=hashlib.sha256(data).hexdigest()
    if (len(data),data.count(b'\n'),sha)!=(expected['bytes'],expected['lf'],expected['sha256']):
        raise ValueError('Canonical byte/LF/hash mismatch')
    pos=data.find(b'BEGIN_SOURCE S1 ')
    if pos<0 or (pos and data[pos-1]!=10): raise ValueError('Missing S1')
    rows=[]
    for i,declared in enumerate(expected['sources'],1):
        h=HEADER.match(data,pos)
        if h is None or h[1]!=f'S{i}'.encode(): raise ValueError('Invalid frame order')
        start=h.end(); end=start+int(h[3]); body=data[start:end]
        body.decode('utf-8',errors='strict')
        row={'id':h[1].decode(),'name':h[2].decode(),'bytes':len(body),
             'lf':body.count(b'\n'),'sha256':hashlib.sha256(body).hexdigest(),
             'start_line':data[:start].count(b'\n')+1,'end_line':data[:end].count(b'\n')}
        if row!=declared or row['bytes']!=int(h[3]) or row['lf']!=int(h[4]) or row['sha256']!=h[5].decode():
            raise ValueError(f'Invalid body S{i}')
        suffix=f'\nEND_SOURCE S{i}\n'.encode()
        if data[end:end+len(suffix)]!=suffix: raise ValueError(f'Invalid end S{i}')
        pos=end+len(suffix)
        while pos<len(data) and data[pos:pos+1] in (b'\n',b'\r',b' ',b'\t'): pos+=1
        rows.append(row)
    if pos!=len(data): raise ValueError('Unexpected trailing bytes')
    return {'canonical_file':expected['file'],'canonical_bytes':len(data),'canonical_lf':data.count(b'\n'),
            'canonical_sha256':sha,'source_count':len(rows),'all_body_frames_match':True,
            'historical_code_executed':False,'hashes_certify_mathematics':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('canonical_txt',type=Path)
    args=p.parse_args(); root=Path(__file__).resolve().parent
    expected=json.loads((root/'q42_source_manifest.json').read_text())
    result=inspect(args.canonical_txt.read_bytes(),expected)
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (root/'q42_source_verification.json').write_text(text); print(text,end='')

if __name__=='__main__': main()
```
END_Q42_ASSET

### `q42_source_verification.json`

BEGIN_Q42_ASSET q42_source_verification.json BYTES=358 SHA256=329eed58231fdaf90aaca52c503b5c0cbafb6cbc4f61250c18d35c5f6443199a
```json
{
  "all_body_frames_match": true,
  "canonical_bytes": 117726,
  "canonical_file": "PROSHKA_CCM_COFINAL_SHORT_MOBIUS_JOINT_Q42_2026-10-26.txt",
  "canonical_lf": 2030,
  "canonical_sha256": "d4ce7e99338317abb4382a00f0baaa5e6808221eb71543360b94b76535d444d6",
  "hashes_certify_mathematics": false,
  "historical_code_executed": false,
  "source_count": 10
}
```
END_Q42_ASSET

