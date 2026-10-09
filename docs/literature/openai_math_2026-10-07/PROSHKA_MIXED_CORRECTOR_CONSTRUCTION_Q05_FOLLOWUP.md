# STATUS: TRY_Q05_MIXED_CORRECTOR_KERNEL_ELIMINATION
```yaml
OPERATIVE_CLASS: TRY_Q05_MIXED_CORRECTOR_KERNEL_ELIMINATION
ARTIFACT_KIND: CONSTRUCTIVE_MATHEMATICAL_FOLLOWUP
QUESTION_INDEX: Q05_FOLLOWUP_NOT_Q06
REQUEST_BASIS: PROSHKA_RATIONAL_HIGH_VALUES_Q05.txt
USER_FOLLOWUP: BUILD_MIXED_CORRECTOR_WITH_POSITIVE_REMAINDER_AT_REQUIRED_BUDGET
REQUEST_SHA256: 04569d150a39475d0e16dcc5a08e61fda25e1b338d9b76cf5ce58c6424902581
PREVIOUS_OPERATOR_NOTE_SHA256: e7c7dd64105f935f1d0fba411b9f8c44929a77cf8dbc0e26b4dfc37fbff713fb
PROTOCOL_REPOSITORY: Malaeu/chen_q3
PROTOCOL_BRANCH: rh_clean
PROTOCOL_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
route_id: RH_SOURCE_ARITHMETIC
front_id: COMPENSATED_JOINT_LOW_PROBE
source_object_family_id: OPENAI_003_COMPLETE_CUBIC_THETA_PROBE
terminal_consumer_id: COMMON_SIGNAL_ZERO_FREE_TO_CRITICAL_LINE
honesty_state: CHALLENGER_NOT_RH
convention_lock_id: OPENAI_ADC7F124_FIXED_DATA_ALL_ZERO_MASKS
EXPLICIT_MIXED_CORRECTOR: CONSTRUCTED_MC_12
TARGET_BUDGET_POSITIVITY: NOT_PROVED
FULL_SOURCE_REMAINDER: (BUDGET_MINUS_ORIGINAL_ENERGY)_e1e1star_PLUS_POSITIVE_DIVISOR_SQUARES
NEW_EXACT_CLASSIFICATION: ALL_LOCAL_ANNIHILATORS_SIMULTANEOUSLY_DIAGONALIZED_BY_DIVISOR_ZETA_MATRIX
FULL_UNRESTRICTED_CERTIFICATE_EXISTS_IFF: ORIGINAL_ENERGY_LE_BUDGET
SCOPED_REJECTION:
  CODE: KILL_OMITTED_LIVE_PRIME_ANCHOR_PSD_CERTIFICATE
  KILL_SCOPE: THEOREM_SHAPE
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  KILL_EVIDENCE_KIND: EXACT_KERNEL_VECTOR_ON_ACTUAL_SOURCE_GRAM
  EVIDENCE: MC_7_TO_MC_9_AND_SECTION_10
  FINITE_NEGATIVE_UPPER_ENVELOPE: -4/13
  COFINAL_WITNESS: OMITTED_LIVE_PRIME_SEED_Z_INVERSE_e_r
  DOES_NOT_KILL: FULL_PRIME_CORRECTORS_OR_SOURCE_MOMENT_OR_RH_ROUTE
POSITIVE_REMAINDER_AT_OLD_BUDGET: CONDITIONAL_ON_PREVIOUS_M
ARITHMETIC_EXPONENT_IMPROVEMENT: NONE
MB34_PROVED: false
MF38_PROVED: false
NEW_INVERSE_POWER_GAIN_PROVED: false
NEW_HIGH_POWER_GAIN_PROVED: false
SOURCE_P_M_R_AND_HIGH_TRANSPORT: CONDITIONAL_UNCHANGED
PROGRESS_CLASS: FALSIFICATION_PROGRESS
ADDITIONAL_PROGRESS: REPRESENTATION_PROGRESS_EXPLICIT_FULL_MIXED_CORRECTOR
PROGRESS_SCOPE: INSUFFICIENT_ACTIVE_PRIME_CERTIFICATE_CLASS_NOT_ORIGINAL_MOMENT
FULL_CONSUMER_PROGRESS: NO_NEW_POWER_GAIN
COGNITIVE_OPERATOR: DUALIZE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ROUTE_SCORE: 3
TARGET_COUNTEREXAMPLE: NONE
RH: OPEN
SP: OPEN
PX_RH_CLAIM: NOT_MADE
REPOSITORY_WRITES: NONE
LEAN_ARB_COMPARATOR_RUNS: NONE
EXACT_FINITE_BOOLEAN_CHECKS: 474
```

## 1. Результат: корректор построен; нужная положительность не установлена

**Смешанный корректор теперь задан явной формулой, а не неизвестными матрицами.** Он использует исходную матрицу корреляций и все необходимые простые. Для него доказано точное равенство
\[
\boxed{
\mathscr B e_1e_1^*-G-\mathcal N_Y
=(\mathscr B-\mathcal E_M)e_1e_1^*
 +\tau\,\mathcal Z^*(I-e_1e_1^*)\mathcal Z,
\qquad \tau>0.
}\tag{MC.1}
\]
Здесь \(\mathcal Z f(n)=\sum_{d\mid n}f(d)\) — **делительное преобразование**, а \(\mathcal E_M\) — ровно прежняя полная положительная энергия, не новая оценка или заменённый момент. Вторая часть справа — явная **сумма квадратов**, то есть неотрицательная квадратичная форма.

**Первая часть не оценена в требуемом бюджете.** На настоящем векторе Мёбиуса вся сумма квадратов равна нулю. Поэтому (MC.1) не доказывает \(\mathcal E_M\le\mathscr B\); оно точно показывает, где это неравенство остаётся.

Получен и более сильный отрицательный результат для предыдущего предложения «начать с двух простых». **Глобальный PSD-сертификат прежнего вида, построенный только из аннуляторов выбранных простых, невозможен при пропуске живой верхней простой колонки.** Есть один явный вектор, на котором все такие поправки исчезают, а остаток строго отрицателен при любом размере бюджета. Это опровергает целый класс сертификатов, а не отдельный неудачный подбор коэффициентов. Полный результат и точная граница опровержения — §5.

Наконец, для полного набора аннуляторов доказана **необходимость и достаточность**:
\[
\boxed{
\exists (Y_{\mathfrak p}):\quad
\mathscr B e_1e_1^*-G-
\sum_{\mathfrak p}(\mathcal A_{\mathfrak p}^*Y_{\mathfrak p}
                    +Y_{\mathfrak p}^*\mathcal A_{\mathfrak p})\succeq0
\iff \mathcal E_M\le\mathscr B.
}\tag{MC.2}
\]
Матрицы здесь не ограничены дополнительными условиями локальности или нормы. Следовательно, **одно лишь существование свободного смешанного корректора — точная перезапись исходной оценки, не более слабая новая задача**. Это уточняет прежний ответ, который называл такой сертификат только достаточным.

**Что реально положительно:** с прежним условным моментным бюджетом \(\mathscr B_{\rm old}\) корректор даёт доказанную условную положительность. С требуемым \(HU^{-1/200+\epsilon}(1+T_1)^A\) знак источникового коэффициента остаётся открытым. Новая степень не зачисляется.

## 2. Источники, полномочия и статус используемых утверждений

Это продолжение последней операторной записки по прямому пути Q5, не вопрос 6/10 и не выбор новой задачи из репозитория. Прочитаны предыдущая операторная конструкция, её точный G, ограничения сертификата и возвраты; из Q5 — исходный контракт и использованные далее определения/счётные положения. Не заявляется новый полный аудит всех аналитических доказательств манускрипта.

Локально подтверждены файлы:

| Файл | Байты | LF | SHA-256 |
|---|---:|---:|---|
| `PROSHKA_RATIONAL_HIGH_VALUES_Q05.txt` | 950620 | 19252 | `04569d150a39475d0e16dcc5a08e61fda25e1b338d9b76cf5ce58c6424902581` |
| `PROSHKA_OPERATOR_RETHINK_Q05_FOLLOWUP.md` | 44455 | 711 | `e7c7dd64105f935f1d0fba411b9f8c44929a77cf8dbc0e26b4dfc37fbff713fb` |

Предыдущая записка задаёт G и нулевую поправку в O.9–O.15; её первый логарифмический выбор в O.18–O.22 ещё не является настоящим смешанным положительным сертификатом. fileciteturn36file0L21-L100 fileciteturn36file0L128-L198

Прямой возврат к исходным двум колонкам Мёбиуса разрешён Q5. Рациональный функционал и \(j_C\) не переопределяются: выбран другой разрешённый вход в тот же потребитель. fileciteturn36file1L343-L347

Протокол `PROSHKA_SYSTEM_PROMPT_v2.md` заново прочитан через GitHub-коннектор; blob указан в заголовке. Репозиторий не изменялся. **Lean, Arb и Comparator не запускались.**

Внешне проверена только связь с **леммой устранения матричных переменных**: Meijer et al., *A Unified Non-Strict Finsler Lemma*, arXiv:2403.10306v2, §IV-A, Lemma 4. Там рассматривается условие \(Q+U^TX+X^TU\succeq0\) через ограничение Q на ядро U. Нестрогий случай нельзя бездумно получать из строгого. Ниже нужный комплексный конечномерный случай доказан собственной явной формулой, включая нулевой запас; внешний текст не используется как арифметический моментный вход. citeturn182692view0

Все новые конечные тождества имеют **[ABSTRACT; PAPER]**. Софинальная часть опровержения малого набора простых использует лишь фиксированный полевой счёт простых из пакета, не P/M/R и не равномерность по движущимся проводникам. Прежний количественный момент M и весь высокий возврат остаются **[COFINAL_FAMILY; CONDITIONAL]**.

## 3. Неизменённая энергия и конечное пространство коэффициентов

**[ABSTRACT; PAPER].** Работаем с хорошими идеалами поля \(\mathbb Q(\sqrt{-3})\), исходными первичными образующими, фиксированным S и прежними нулевыми ветвями. Параметры:
\[
 r\in[28/25,113/100],\quad c_0=1/10000,\quad
 D=U^r,\quad H=D^{1+c_0},\quad
 p=\frac{r(1+c_0)-1}{6},\quad P=U^p,
\]
\[
 DU^{-1/100}\le L\le D,\qquad
 \mathscr B=C_*HU^{-\eta+\epsilon}(1+T_1)^A,
 \qquad \eta=1/200.
\]
\(C_*\) — одна константа по фиксированным данным и общей профильной семье, не подбираемая по ячейке или по значению энергии.

Выбираем конечное множество
\[
 \mathcal I_X=\{n\text{ good}:q_n\le X\},\qquad
 X\ge \max_j\beta_j D,
\]
где \(\operatorname{supp}W_j\subset[\alpha_j,\beta_j]\Subset(0,\infty)\). X фиксирован при изменении L в текущей полосе. Множество замкнуто относительно делителей. Координаты всех простых степеней остаются, даже когда \(\mu(n)=0\).

Пусть \(e=e_1\) — вектор единичного **идеала колонки**. Это не элементные единичные строки. Введём
\[
 t_{u,a}(n)=L^{-1/2}\nu(n)\chi_n(u)^{\varepsilon_\chi}
             1_{(n,a)=1}W_j(q_n/L),
\]
\[
 G_{n,m}=\sum_{\substack{a\text{ good}\q_a\le P}}
   \sum_{u^{(6)}}\rho(q_u/U)\,
                  \overline{t_{u,a}(n)}t_{u,a}(m).
\]
Тогда
\[
 \boxed{G\succeq0,\qquad
 \mathcal E_M=\boldsymbol\mu^*G\boldsymbol\mu.}\tag{MC.3}
\]
Все элементные строки, шесть единиц, S-показатели, исходные усилители и их повторные простые сохранены. Нет дополнительного \((u,a)=1\).

Эквивалентная запись:
\[
 G_{n,m}=\frac{\overline{\nu(n)W_j(q_n/L)}\nu(m)W_j(q_m/L)}{L}
 w_P(nm)\sum_{u^{(6)}}\rho(q_u/U)
 \overline{\chi_n(u)^{\varepsilon_\chi}}\chi_m(u)^{\varepsilon_\chi},
\]
\[
 w_P(nm)=\#\{a\text{ good}:q_a\le P,\ (a,nm)=1\}.
\]
Это точный счёт, не плотность и не сжатый вес \(w_{P,Y}(b)\). Исходная матрица записана именно так в O.9–O.11. fileciteturn36file0L21-L51

## 4. Вычисляемые координаты: одновременная диагонализация всех простых

### 4.1. Делительная матрица и её точная обратная

**[ABSTRACT; PAPER].** Определим
\[
 (\mathcal Z f)(n)=\sum_{d\mid n}f(d),\qquad
 (\mathcal Z^{-1}g)(n)=\sum_{d\mid n}\mu(n/d)g(d).
\]
Это конечные матрицы на \(\mathcal I_X\); упорядочение по норме делает \(\mathcal Z\) треугольной с диагональю 1. Проверка обратимости:
\[
 \sum_{d\mid n/m}\mu(d)=1_{n=m}.
\]
Поэтому
\[
 \mathcal Z\boldsymbol\mu=e,\qquad
 \mathcal Z^{-1}e=\boldsymbol\mu,\qquad e^*\mathcal Z=e^*.
\]

### 4.2. Преобразование локального аннулятора

Для каждого хорошего простого \(\mathfrak p\) остаётся прежний оператор
\[
 (\mathcal A_{\mathfrak p}f)(n)
 =v_{\mathfrak p}(n)f(n)
  +\sum_{k=1}^{v_{\mathfrak p}(n)} f(n/\mathfrak p^k).
\]
Пусть \(\mathcal D_{\mathfrak p}\) — диагональная матрица с элементами \(v_{\mathfrak p}(n)\). Тогда
\[
 \boxed{\mathcal Z\mathcal A_{\mathfrak p}
       =\mathcal D_{\mathfrak p}\mathcal Z,
 \qquad
 \mathcal A_{\mathfrak p}
       =\mathcal Z^{-1}\mathcal D_{\mathfrak p}\mathcal Z.}\tag{MC.4}
\]

**Доказательство.** В \((\mathcal Z\mathcal A_{\mathfrak p}f)(n)\) коэффициент при данном \(f(d)\), \(d\mid n\), равен
\[
 v_{\mathfrak p}(d)+\#\{k\ge1:d\mathfrak p^k\mid n\}
 =v_{\mathfrak p}(d)+v_{\mathfrak p}(n)-v_{\mathfrak p}(d)
 =v_{\mathfrak p}(n).
\]
Это коэффициент правой стороны. Все степени участвуют до выполнения суммы. ∎

Следовательно, разные \(\mathcal A_{\mathfrak p}\) не просто коммутируют: у них есть общие явно известные собственные векторы
\[
 f^{(d)}=\mathcal Z^{-1}e_d,
 \qquad f^{(d)}(n)=1_{d\mid n}\mu(n/d),
\]
\[
 \mathcal A_{\mathfrak p}f^{(d)}=v_{\mathfrak p}(d)f^{(d)}.
 \tag{MC.5}
\]

Это **не унитарная** смена координат. Для квадратичных форм далее используется конгруэнция, сохраняющая знак, а не ложное равенство операторных норм.

### 4.3. Что остаётся при неполном наборе простых

Пусть \(\mathcal P\) — выбранный конечный набор хороших простых. Введём
\[
 d_{\mathcal P}(n)=\sum_{\mathfrak p\in\mathcal P}v_{\mathfrak p}(n),
 \qquad \mathcal D_{\mathcal P}=\operatorname{diag}d_{\mathcal P}(n),
\]
\[
 F_{\mathcal P}=\operatorname{diag}1_{d_{\mathcal P}(n)=0},
 \qquad K_{\mathcal P}=I-F_{\mathcal P}.
\]
Точное совместное ядро равно
\[
 \boxed{\bigcap_{\mathfrak p\in\mathcal P}\ker\mathcal A_{\mathfrak p}
 =\operatorname{span}\{f^{(d)}:d_{\mathcal P}(d)=0\}.}\tag{MC.6}
\]
При всех простых \(q_{\mathfrak p}\le X\) оно одномерно и равно \(\operatorname{span}\{\boldsymbol\mu\}\). При двух простых остаются все прочие простые ядра, а не один Мёбиус. Прежнее доказательство одномерности для **полного** набора не позволяло автоматически использовать ту же одномерность для двух простых. fileciteturn37file1L32-L48

## 5. Почему двухпростой глобальный сертификат прежней формы не проходит

### 5.1. Один свидетель против всех поправок выбранного набора

**[ABSTRACT; PAPER].** Пусть хороший простой \(\mathfrak r\notin\mathcal P\) лежит на живой верхней части колоночного окна:
\[
 W_j(q_{\mathfrak r}/L)\ne0,\qquad
 7q_{\mathfrak r}>\beta_jL.
 \tag{MC.7}
\]
Число 7 — минимальная норма неединичного хорошего идеала. Возьмём
\[
 f=f^{(\mathfrak r)}=\mathcal Z^{-1}e_{\mathfrak r}.
\]
Тогда \(f(1)=0\) и \(\mathcal A_{\mathfrak p}f=0\) при всех \(\mathfrak p\in\mathcal P\).

У \(f\) сохранены все координаты \(\mathfrak r m\) до X. Но в исходном профиле из них остаётся только \(m=1\): при любом неединичном хорошем m,
\(q_{\mathfrak r m}\ge7q_{\mathfrak r}>\beta_jL\). Следовательно,
\[
 f^*Gf=G_{\mathfrak r,\mathfrak r}.
\]
Для **любых** матриц \(Y_{\mathfrak p}\), любых смешанных коэффициентов внутри них и любого бюджета \(\mathscr B\):
\[
 \boxed{
 f^*\left[\mathscr B ee^*-G-
   \sum_{\mathfrak p\in\mathcal P}
    (\mathcal A_{\mathfrak p}^*Y_{\mathfrak p}
      +Y_{\mathfrak p}^*\mathcal A_{\mathfrak p})\right]f
 =-G_{\mathfrak r,\mathfrak r}.
 }\tag{MC.8}
\]
Если диагональ положительна, глобальная PSD-цель невозможна **при любом бюджете**, поскольку бюджет на этом векторе равен нулю.

Это касается также добавления смешанных блоков
\(\mathcal A_{\mathfrak p}^*B_{\mathfrak p,\mathfrak q}\mathcal A_{\mathfrak q}\)
и иных поправок, чьи квадратичные формы исчезают на совместном ядре выбранных ограничений. Не утверждается такой вывод для произвольного оператора, не удовлетворяющего этому условию.

### 5.2. Положительная диагональ на самой исходной семье

Если дополнительно
\(q_{\mathfrak r}>\max(P,\beta_\rho U)\), то \(\mathfrak r\) не делит ни один исходный усилитель a и ни одну ненулевую строку u на носителе \(\rho\). Поэтому **точно**
\[
 G_{\mathfrak r,\mathfrak r}
 =\frac{|W_j(q_{\mathfrak r}/L)|^2}{L}
 \underbrace{\#\{a\text{ good}:q_a\le P\}
              \sum_{u^{(6)}}\rho(q_u/U)}_{\mathfrak m_{U,P}}.
 \tag{MC.9}
\]
Никакой независимости масок или случайных фаз здесь нет. Использован их настоящий ненулевой модуль; \(|\nu(\mathfrak r)|=1\), потому что простой хороший.

**[COFINAL_FAMILY; PAPER, с фиксированным полевым счётом простых].** Для любого фиксированного ненулевого профиля W можно взять интервал в его ненулевой верхней части выше \(\sup\operatorname{supp}W/7\). Он содержит \(\gg L/\log L\) хороших простых при больших L. На исходной полосе \(L\ge U^{1.11}\), поэтому их нормы больше \(P\) и \(\beta_\rho U\) для достаточно больших U. Ненулевая неотрицательная \(\rho\) даёт непустую строковую массу: достаточно простых элементных строк в её фиксированном аннулярном интервале, включая все их единичные кратности.

Используется только фиксированный счёт простых идеалов из источника; он не зависит от движущегося Hecke-проводника. fileciteturn37file0L7-L25

Следовательно, набор из двух простых — даже выбираемых по U — пропускает живую верхнюю простую колонку. Более общо, любой выбранный набор, не содержащий всех таких простых, имеет препятствие (MC.8). Набор малых простых \(q_{\mathfrak p}\le U^{1/80}\) тем более не достаточен для этого глобального сертификата.

**Scope опровержения:** матричный сертификат с правой частью только \(\mathscr B ee^*\), глобальной PSD-проверкой и ограничениями выбранного неполного набора. Не опровергнуты исходная энергия, MB.34, смешанные корректоры с полным набором, локальные промежуточные тождества с сохранённым дополнением или другая бюджетная форма с доказанной ценой на Мёбиусе.

**Слабейший ремонт:** сохранить весь неподавленный блок \(F_{\mathcal P}\widehat G F_{\mathcal P}\), а не объявлять его положительно оплаченным. Следующий раздел делает именно это; при полном наборе остаётся один источниковый коэффициент.

## 6. Явная смешанная конструкция для любого набора простых

### 6.1. Формула без поиска неизвестных множителей

**[ABSTRACT; PAPER].** Для краткости пишем \(F=F_{\mathcal P}\), \(K=I-F\), \(\mathcal D=\mathcal D_{\mathcal P}\). Определим
\[
 \widehat G=\mathcal Z^{-*}G\mathcal Z^{-1},\qquad
 \mathcal D^\dagger_{n,n}=
 \begin{cases}1/d_{\mathcal P}(n),&d_{\mathcal P}(n)>0,\\0,&d_{\mathcal P}(n)=0.
 \end{cases}
 \tag{MC.10}
\]
Здесь \(\mathcal D^\dagger\) — просто диагональная обратная на ненулевых координатах, не неизвестный обратный арифметический оператор. Пусть \(\tau>0\) задано заранее, например \(\tau=1\).

Положим
\[
 B_{\mathcal P,\tau}
 =-\tfrac12 K\widehat G K-K\widehat G F-\tfrac\tau2K,
 \tag{MC.11}
\]
\[
 \boxed{
 Y_{\mathfrak p}=Y_{\mathcal P,\tau}
 :=\mathcal Z^*\mathcal D^\dagger
          B_{\mathcal P,\tau}\mathcal Z,
 \qquad \mathfrak p\in\mathcal P.
 }\tag{MC.12}
\]
При пустом \(\mathcal P\) поправка нулевая, F=I. Для непустого набора одинаковый Y у каждого простого является допустимой конструкцией: сумма аннуляторов уже содержит выбранные локальные ограничения. Y вообще не диагонален и смешивает оба индекса полного G.

Это конечная формула через известные делительные матрицы и настоящий G, без решения SDP и без предположения \(\mathcal E_M\le\mathscr B\). В неё **не подставляется неизвестная энергия как отдельно заданный малый параметр**. Однако величина энергии останется в итоговом коэффициенте; это не скрывается.

### 6.2. Проверка всех блоков и знаков

Пусть
\[
 \mathcal A_{\mathcal P}=\sum_{\mathfrak p\in\mathcal P}\mathcal A_{\mathfrak p}
   =\mathcal Z^{-1}\mathcal D\mathcal Z,
 \qquad \mathcal N_Y=\mathcal A_{\mathcal P}^*Y+Y^*\mathcal A_{\mathcal P}.
\]
Из \(\mathcal D\mathcal D^\dagger=K\) и \(KB_{\mathcal P,\tau}=B_{\mathcal P,\tau}\) следует
\[
 \mathcal N_Y=\mathcal Z^*
       (B_{\mathcal P,\tau}+B_{\mathcal P,\tau}^*)\mathcal Z.
\]
Сумма в скобках равна
\[
 -K\widehat G K-K\widehat G F-F\widehat G K-\tau K
 =-\widehat G+F\widehat G F-\tau K.
\]
Следовательно,
\[
 \boxed{G+\mathcal N_Y
 =\mathcal Z^*(F\widehat G F-\tau K)\mathcal Z.}\tag{MC.13}
\]
Ни одной раздельной оценки смешанных простых здесь нет: все их точные коэффициенты вошли в матричное сокращение.

Полный остаток имеет вид
\[
 \boxed{
 R_{\mathcal P,\tau}
 =\mathscr B ee^*-G-\mathcal N_Y
 =\mathcal Z^*\{\mathscr B ee^*-F\widehat G F+\tau K\}\mathcal Z.
 }\tag{MC.14}
\]
Именно неподавленный блок F объясняет препятствие §5. На нём аннуляторы не дают ни одной поправки.

### 6.3. Где находятся настоящие смешанные простые

Элементы преобразованного G равны
\[
 \widehat G_{d,e}
 =\sum_{\substack{n,m\in\mathcal I_X\\d\mid n,
                                      \ e\mid m}}
    \mu(n/d)\mu(m/e)G_{n,m}.
 \tag{MC.15}
\]
Обе колонки, их фактические нормировки, общий строковый коррелят, исходный \(w_P(nm)\) и все нули внутри G остаются. Это не произведение двух оценённых независимо сумм.

На минимальном делительном блоке \(\{1,\mathfrak p,\mathfrak q,\mathfrak p\mathfrak q\}\)
\[
 \mathcal Z=\begin{pmatrix}
 1&0&0&0\\1&1&0&0\\1&0&1&0\\1&1&1&1
 \end{pmatrix},\qquad
 \mathcal Z^{-1}=\begin{pmatrix}
 1&0&0&0\\-1&1&0&0\\-1&0&1&0\\1&-1&-1&1
 \end{pmatrix}.
\]
Последняя строка содержит смешанное включение–исключение. В полном \(\mathcal I_X\) это не усечение на четыре колонки: сохраняются все степени и другие простые. Четырёхмерная запись служит только иллюстрацией локального блока.

## 7. Полный набор простых: сумма квадратов и единственный неизменяемый коэффициент

При \(\mathcal P=\{\mathfrak p\text{ good}:q_{\mathfrak p}\le X\}\) имеем \(F=ee^*\). Поэтому
\[
 F\widehat G F=\widehat G_{1,1}ee^*,\qquad
 \widehat G_{1,1}
 =e^*\mathcal Z^{-*}G\mathcal Z^{-1}e
 =\boldsymbol\mu^*G\boldsymbol\mu=\mathcal E_M.
 \tag{MC.16}
\]
Это доказывает (MC.1). Для любого вектора x:
\[
 \boxed{
 x^*R_\tau x
 =(\mathscr B-\mathcal E_M)|x(1)|^2
   +\tau\sum_{\substack{n\in\mathcal I_X\\n\ne1}}
          \left|\sum_{d\mid n}x(d)\right|^2.
 }\tag{MC.17}
\]

Отсюда без численного вычисления собственных значений:

* если \(\mathscr B>\mathcal E_M\), R положительно определён на текущем конечном пространстве;
* если \(\mathscr B=\mathcal E_M\), R положительно полуопределён, и его ядро равно \(\operatorname{span}\{\boldsymbol\mu\}\);
* если \(\mathscr B<\mathcal E_M\), R имеет ровно одно отрицательное направление по инерции; свидетель — сам \(\boldsymbol\mu\).

Это утверждение об **инерции квадратичной формы**, то есть числе знаков после обратимой смены координат. Оно не утверждает, что исходные евклидовы собственные значения равны \(\mathscr B-\mathcal E_M,\tau,\ldots,\tau\), и не даёт независимого от X спектрального зазора.

Увеличение \(\tau\) не меняет источниковый запас:
\[
 \boldsymbol\mu^*R_\tau\boldsymbol\mu
 =\mathscr B-\mathcal E_M,
 \qquad
 (I-ee^*)\mathcal Z\boldsymbol\mu=0.
\]
Таким образом, «сделать положительную штрафную часть огромной» не исправляет недоказанный знак на настоящем источнике.

## 8. Это полный ответ для свободных нулевых поправок, не только один выбор Y

### 8.1. Необходимость одного и того же запаса для любого корректора

Для любого допустимого Y по-прежнему
\[
 \boldsymbol\mu^*\mathcal N_Y\boldsymbol\mu=0.
\]
Следовательно, \(R_Y\succeq0\) обязательно влечёт
\(\mathscr B-\mathcal E_M\ge0\). Конструкция §6–7 даёт обратное направление и тем самым доказывает (MC.2), в том числе при равенстве бюджета и энергии.

### 8.2. Все эрмитовы нулевые формы уже порождены локальными аннуляторами

**[ABSTRACT; PAPER].** Для полного набора простых
\[
 \boxed{
 \left\{\sum_{\mathfrak p}
   (\mathcal A_{\mathfrak p}^*Y_{\mathfrak p}
       +Y_{\mathfrak p}^*\mathcal A_{\mathfrak p})\right\}
 =\{N=N^*: \boldsymbol\mu^*N\boldsymbol\mu=0\}.
 }\tag{MC.18}
\]

Включение слева направо уже доказано. Для обратного возьмём такую N и \(\widehat N=\mathcal Z^{-*}N\mathcal Z^{-1}\). Тогда \(\widehat N_{1,1}=0\). Положим \(F=ee^*,K=I-F\) и
\[
 B_N=\tfrac12K\widehat N K+K\widehat N F.
\]
Получаем \(B_N+B_N^*=\widehat N\). Матрица
\(Y_N=\mathcal Z^*\mathcal D^\dagger B_N\mathcal Z\), одинаковая при всех простых, даёт требуемую N. ∎

Значит, добавление форм более высокой смешанности, которые всё равно обнуляются на Мёбиусе, не расширяет **этот неограниченный матричный класс**. Ограниченный разреженный класс может быть вычислительно удобнее, но не получает автоматического нового источникового знака.

### 8.3. Один двойственный свидетель для всего класса

Матрица \(Z_{\rm dual}=\boldsymbol\mu\boldsymbol\mu^*\succeq0\) удовлетворяет
\[
 \operatorname{tr}(ee^*Z_{\rm dual})=1,\quad
 \operatorname{tr}(\mathcal N_Y Z_{\rm dual})=0,\quad
 \operatorname{tr}(G Z_{\rm dual})=\mathcal E_M.
\]
Поэтому задача свободного подбора корректоров имеет точный оптимум
\[
 \boxed{\inf\{b:\exists Y,\ b ee^*-G-\mathcal N_Y\succeq0\}
       =\mathcal E_M,}\tag{MC.19}
\]
и оптимум достигается конструкцией выше при \(b=\mathcal E_M\). Это не способ вычислить малую энергию без её оценки. Это проверка, что большой SDP-поиск не обязан извлечь дополнительный арифметический выигрыш из одних равенств.

**Важная граница:** эквивалентность не делает метод неправильным. Явный структурированный Y с независимым доказательством знака всё ещё был бы настоящим доказательством нужного момента. Необоснованной была бы лишь надежда, что существование свободных множителей само по себе легче, чем исходный знак.

### 8.4. Почему полная смешанная поправка не равна одному штрафу

При бюджете \(b=\mathcal E_M\) простая поправка вида \(+t\sum\mathcal A_{\mathfrak p}^*\mathcal A_{\mathfrak p}\) к остатку имеет нулевую квадратичную форму на \(\mu\), но её действие на \(\mu\) равно
\(\mathcal E_M e-G\mu\). Если этот вектор ненулевой, остаток не может быть PSD: для PSD-матрицы нулевое значение квадратичной формы требует принадлежности вектора ядру. Ни один t это не исправит.

Полный Y в (MC.12) **действительно убирает эти поперечные смешанные блоки** и работает при нулевом запасе. Это конкретная выполненная часть конструкции, но она не оценивает сам запас \(\mathscr B-\mathcal E_M\).

## 9. Работа с настоящим арифметическим бюджетом

### 9.1. Где положительность уже доказана

**[COFINAL_FAMILY; CONDITIONAL на прежнем масочном M].** Исходный вход даёт
\[
 \mathcal E_M\le\mathscr B_{\rm old},\qquad
 \mathscr B_{\rm old}
 =C_{M,\epsilon,\mathcal F}P
        \{U+U^{1/6}L^{5/6}\}U^\epsilon(1+T_1)^{A_M}.
 \tag{MC.20}
\]
Подстановка \(\mathscr B_{\rm old}\) в (MC.17) доказывает PSD-остаток для всего исходного семейства, условно на этом моменте. Никакого дополнительного входа P для нового G не нужно. R используется только в прежнем сравнительном возврате.

Есть и безусловный конечный бюджет: из \(|\mu|\le1\), \(|\psi|\le1\)
\[
 \mathcal E_M\le
 \mathscr B_{\rm abs}:=
 \frac{\mathfrak m_{U,P}}L
    \left(\sum_{n\text{ good}}|W_j(q_n/L)|\right)^2
 \ll PU L\,(1+T_1)^{A_0}.
 \tag{MC.21}
\]
При нём тот же явный остаток тоже PSD, но цена гораздо хуже нужной. Положительность при слишком большом бюджете не выдается за решение.

### 9.2. Точный дефицит прежнего верхнего конверта

На \(L=D=U^r\) длинный член (MC.20) имеет показатель
\[
 p+\frac16+\frac{5r}6=r+\frac{rc_0}6.
\]
Показатель целевого бюджета равен \(r(1+c_0)-\eta\). Их разность:
\[
 \boxed{\eta-\frac{5rc_0}6.}\tag{MC.22}
\]
При \(\eta=1/200\):

| r | Недостающая степень старого конверта |
|---|---:|
| \(28/25\) | \(46/9375\) |
| \(113/100\) | \(5887/1200000\) |

Это **недостаточность верхней оценки**, не положительная нижняя оценка истинной энергии и не отрицательный свидетель для целевого бюджета. Для каждого фиксированного достаточно малого \(\epsilon\) остаётся этот положительный степенной дефицит.

Увеличение числа смешанных аннуляторов после полного охвата, параметра \(\tau\), размера X или количества итераций не уменьшает (MC.22): источниковый коэффициент (MC.16) не меняется. Это точное заключение об данной конструкции, а не запрет искать новое арифметическое доказательство оценки G.

### 9.3. Первый неоплаченный член выписан без свободного корректора

\[
\boxed{
\begin{aligned}
 \widehat G_{1,1}=\frac1L
 \sum_{n,m\text{ good}}
 &\mu(n)\mu(m)\overline{\nu(n)W_j(q_n/L)}
                    \nu(m)W_j(q_m/L)\,w_P(nm)\\
 &\times\sum_{u^{(6)}}\rho(q_u/U)
      \overline{\chi_n(u)^{\varepsilon_\chi}}
                   \chi_m(u)^{\varepsilon_\chi}.
\end{aligned}}
\tag{MC.23}
\]
Он вещественен и неотрицателен, поскольку равен (MC.3). Все исходные члены присутствуют. Сокращение поперечных блоков не сделало (MC.23) меньшим объектом: **это вся исходная энергия**. Поэтому нынешняя работа не засчитывается как новый моментный выигрыш.

После прежнего оплаченного сравнения и диагонали остаётся ровно прежняя MB.34, а не новая обязательная лемма о существовании Y. Независимой достаточной верхней оценки (MC.23) в требуемом бюджете здесь нет.

## 10. Точный конечный источник и проверки знака

### 10.1. Полная диагностическая ячейка, не выбранные удобные строки

**[FINITE_CELL; PAPER].** Берём прежние диагностические фиксированные данные:
\(U=49,L=78,r=28/25,\nu=1,S=\{\mathfrak p:\mathfrak p\mid6\}\).
Профиль W гладкий, поддержан в \((6.5/78,7.5/78)\), \(W(7/78)=2\).
Профиль \(\rho\) гладкий неотрицательный, поддержан в
\((48.5/49,49.5/49)\), \(\rho(1)=1\).
Это **фиксированные диагностические профили**, не утверждение о значении фактического глобального источникового профиля.

Точное включение в масштабную полосу проверяется целыми неравенствами
\(78^{25}\le49^{28}\), \(78^{100}\ge49^{111}\).
На этой ячейке \(P<2\), поэтому единственный усилитель — единичный идеал. Берём полное \(\mathcal I_{83}\), содержащее 25 хороших идеалов, в том числе все их простые степени до этой нормы. Такой X с запасом покрывает колоночный профиль.

Простые над 7:
\[
 \pi=-2-3\omega,\qquad \bar\pi=1+3\omega.
\]
Все 18 элементных строк нормы 49 — три единичные орбиты
\(\zeta7,\zeta\pi^2,\zeta\bar\pi^2\). На каждой строке хотя бы один из двух символов нулевой. Поэтому исходная матрица G, **для M, а не J**, имеет лишь два ненулевых элемента:
\[
 G_{\pi,\pi}=G_{\bar\pi,\bar\pi}=\frac4{13},\qquad
 \boxed{\mathcal E_M=\frac8{13}.}\tag{MC.24}
\]
Нормировка: у каждой колонки 6 ненулевых строк, каждый квадрат коэффициента равен \(4/78\); значит, диагональ \(24/78=4/13\). Перекрёстные элементы нулевые по буквальным исходным нулям, не по предположению о случайности фаз. Обе ориентации символа дают ту же матрицу.

### 10.2. Проверка всего двухпростого класса

Выберем активные \(\pi\) и \(\sigma=1-3\omega\) нормы 13, но не \(\bar\pi\). Вектор
\(f=\mathcal Z^{-1}e_{\bar\pi}\) обнуляет оба аннулятора. По (MC.8)
\[
 \boxed{f^*R_Yf=-\frac4{13}<0}\tag{MC.25}
\]
при любом бюджете и любом Y выбранного класса. В коде дополнительно проверены бюджеты 0, \(8/13\) и \(10^9\); универсальность по бюджету и Y следует из доказательства, не из трёх чисел.

Это опровержение предложенного **PSD-сертификата на всём пространстве**, где такой тестовый вектор законен. Оно не подменяет настоящий коэффициент \(\mu\) другим вектором в целевой энергии и не опровергает сам момент.

### 10.3. Полная поправка и граничный знак

Для всех 21 хороших простых идеалов до нормы 83 при \(\tau=1\) получена точная конгруэнция
\[
 \mathcal Z^{-*}R_\tau\mathcal Z^{-1}
 =\operatorname{diag}(\mathscr B-8/13,1,\ldots,1).
\]
При бюджетах \(7/13,8/13,9/13\) первый диагональный коэффициент равен соответственно \(-1/13,0,1/13\). Это проверяет отрицательную, нестрогую положительную и строгую положительную ветви. Данные бюджеты — тестовые уровни относительно известной конечной энергии, **не заявленная софинальная константа целевой оценки**.

### 10.4. Что было зарегистрировано и реально выполнено

Перед новыми конечными запусками сохранены P1–P5. Регистрация следует бумажному поиску, но предшествует выполнению кода; она не изображается предсказанием ещё не выведенной формулы.

| Прогноз | Судьба |
|---|---|
| P1: делительная диагонализация и \(\mathcal Z\mu=e\) | Подтверждён |
| P2: смешанная поправка сохраняет только блок совместного ядра и явный штраф | Подтверждён |
| P3: пропущенный сопряжённый простой даёт \(-4/13\) | Подтверждён |
| P4: полный остаток имеет источниковый коэффициент \(\mathscr B-\mathcal E_M\) | Подтверждён во всех трёх знаковых ветвях |
| P5: удаление старшей степени и порча \(\mu(\pi\bar\pi)\) обнаруживаются | Подтверждён |

Выполнены **474 точные булевы проверки**. Одна проверка матричного равенства — одна проверка, а не искусственно раздутый счёт по элементам. Использованы полные множества хороших идеалов до норм 30 и 83, точные рациональные/гауссовы рациональные матрицы, а также полная диагностическая источник-ячейка выше. Дополнительные комплексные матрицы Грама служат **только общими алгебраическими контролями**; они не выдаются за исходную арифметику.

Отрицательные контроли: оставление только первого степенного сдвига даёт \(-1\) на \(\pi^2\); замена настоящего \(\mu(\pi\bar\pi)=1\) на 0 также даёт дефект \(-1\). Ни один софинальный момент не сертифицирован этими проверками.

## 11. Возврат к MB.34 и всем исходным обязательствам

**[COFINAL_FAMILY; CONDITIONAL, недоказанный новый вход].** При возможной будущей оценке (MC.23) со степенью \(\eta\) сначала получается полная положительная энергия. Тогда исходный эксцесс не превосходит её, и рациональное представление Q5 не требуется для данного прямого пути.

Прежние точные равенства сохраняются:
\[
 \mathfrak D_{\rm off}=\mathcal E_M-\lambda\mathcal R_H
                              -\mathfrak D_{\rm diag},\qquad
 \mathfrak C_G=\mathfrak D_{\rm off}+\mathcal R_{\rm paid}.
\]
Сохраняются \(0\le\lambda\mathcal R_H\ll PU\) с условной ценой R,
\(|\mathfrak D_{\rm diag}|\ll PU\) и прежний конверт
\[
 |\mathcal R_{\rm paid}|
 \ll HU^{-1/200-257/75000+\epsilon}(1+T_1)^A.
\]
Никакая диагональ не удалена из G и не оплачена дважды. Сырые главные строки в сравнении, все S-показатели, прежний внешний g, его граница, нижнее окно и двухсдвиговые возвраты остаются частью прежнего контракта.

Конструкция выполняется для каждого **общего производного профиля** до строкового выбора параметров. X покрывает всю полосу; фазовые или нулевые данные не дифференцируются. После положительной энергетической оценки применяется прежний **Соболевский возврат**, а не производная неизвестного Y или селектора.

Конечное обращение:
\[
 M_u(D;W)=\sum_{d\mid\operatorname{rad}a}
       \frac{\mu(d)\psi_u(d)}{\sqrt{q_d}}
                         M_{ua^6}(D/q_d;W).
\]
Все исходные a, общие простые u,a, масштабы \(D/q_d\), обе границы полосы и общие профили сохранены. Соответствующий показатель был бы
\[
 \frac HP U^{-\eta+\epsilon}(1+T_1)^A
 =U^{(1+5r)/6-\{\eta-5rc_0/6\}+\epsilon}(1+T_1)^A.
\]
При \(\eta=1/200\) минимальный запас до потерь равен \(5887/1200000\). Чтобы оставить \(\theta=1/250\), совокупные потери, включая высоту, должны быть меньше \(1087/1200000\). Любая меньшая \(\eta\) должна превосходить \(113/1200000\) плюс все фактические потери. Этот контракт прямо сохранён запросом и предыдущим ответом. fileciteturn36file1L345-L347 fileciteturn36file0L241-L264

**Нужный вход не доказан; нового обратного или высокого выигрыша нет.** Математическая корректность явной конечной поправки не сертифицирует аналитические предпосылки P/M/R.

## 12. Итоговый выбор, самоатака и эпистемический реестр

### 12.1. Сильнейшее возражение

**«Ты построил матрицу, в которой осталась исходная энергия. Это ещё не требуемый положительный остаток».** Верно. Поэтому ответ не имеет статуса PASS для нужного бюджета. Построены все корректирующие блоки и доказана их полная граница: малого набора ограничений недостаточно, а полный свободный класс равносилен исходной скалярной оценке.

Нельзя рекламировать эту эквивалентность как новый арифметический выигрыш. Но нельзя и объявлять на её основании исходную оценку ложной. Корректор с независимым источниковым доказательством знака остаётся допустимым способом доказательства.

### 12.2. Три проверенных связи

**Алгебра делителей — EXACT_ISOMORPHISM:** (MC.4) одновременно диагонализует все локальные аннуляторы; mixed-простые не создают неизвестного нового спектра.

**Ограниченные квадратичные формы — FORM_IDENTITY:** (MC.12)–(MC.17) выполняют точное устранение поперечных блоков с проверкой нестрогого граничного случая. Внешняя лемма проверена как контекст; арифметического конверта она не приносит.

**Двойственный положительный свидетель — ONE_WAY_CERTIFICATE и точный оптимум:** \(\mu\mu^*\) фиксирует бюджет для всех корректоров одновременно, (MC.19). Количество свободных матриц не обходит этот свидетель.

### 12.3. Два допустимых дальнейших представления

| Представление | Что действительно должно измениться | Решающая сила / стоимость |
|---|---|---|
| **Исходная невыбранная MB.29** с обеими колонками \(\mu\) и точной мерой \(\Omega-\lambda\) | Новая совместная верхняя оценка строкового арифметического коррелята, прежде чем он заменён отдельными модулями. Все сравнительные и диагональные члены уже имеют свои прежние цены. | 5/5 / 5/5. Это прямой путь к потребителю, без свободного поиска Y. |
| **Оконный коммутатор аннулятора** из O.23–O.24 | Новая совместная оценка \([\mathcal A_{\mathfrak p},\mathcal W_L]\mu\) с исходными строками и всеми смешанными степенями; нужен ограниченный возврат, а не малость по гладкости или новый полный масштабный контракт. | 5/5 / 4/5. Риск: возвращение всей энергии с коэффициентом один. |

Оценки — относительные стоимость/решающая сила, не вероятности успеха. Эти строки не являются дополнительными доказанными поставщиками. Ни один большой запуск не разрешается простой сменой представления.

**Выбранное действие по результату этого расчёта:** больше не искать свободные матричные множители как отдельную недостающую теорему. Они построены. Количественная обязанность остаётся MB.34 или её прямым положительным энергетическим входом (MC.23). Следующий арифметический тест должен менять оценку этого члена, а не произвольную положительность на дополнении к источнику.

### 12.4. Различающие величины

Для ограниченного набора простых точный **DISCRIMINATOR** — (MC.8). Его строгая отрицательная верхняя огибающая опровергает конкретный сертификатный класс; в конечном источнике она равна \(-4/13\).

Для полного класса **DISCRIMINATOR** есть
\[
 \mathscr D(U,L,W_j)
 =C_*HU^{-\eta+\epsilon}(1+T_1)^A-\mathcal E_M(U,L,W_j).
\]
Для PASS требуется доказанная нижняя огибающая \(\mathscr D\ge0\) с одной константой на всей области. Для KILL конкретного целевого конверта нужна строгая отрицательная верхняя огибающая **этой** величины на допустимом источнике; такой огибающей не получено. Нулевые тождества аннулятора и конечные тесты иной бюджетной константы не заменяют этот критерий.

### 12.5. Закрытие итерации

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: COMMON_SIGNAL_ZERO_FREE_TO_CRITICAL_LINE
  ACTUAL_CONSUMER_REQUIREMENT: ORIGINAL_JOINT_BOUND_WITH_COMPLETE_POSITIVE_ENERGY_RETURNS
  ORIGINAL_REQUESTED_OBJECT: MIXED_NULL_CORRECTOR_WITH_TARGET_BUDGET_PSD_REMAINDER
  ORIGINAL_OBJECT_IS: UNKNOWN
  LOCAL_EQUIVALENCE: >-
    In the unrestricted full-annihilator finite matrix class, existence of
    the proposed anchored PSD corrector is necessary and sufficient for
    the original finite positive energy bound, not an independent supplier.
  KNOWN_WEAKER_INTERFACES:
    - DIRECT_MB34_WITH_PAID_COMPARISON_AND_DIAGONAL
    - ORIGINAL_MF38_WITH_PAID_SMALL_VALUES
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: >-
    Explicit simultaneous divisor diagonalization, complete mixed
    elimination formula, omitted-live-prime kernel witness on the actual
    Gram, and exact characterization of every unrestricted null correction.
  REOPEN_TRIGGER: >-
    A new source-specific joint estimate of MC23 or MB34 with eta exceeding
    the inherited 113/1200000 return cost and every actual height loss.
  MATHEMATICALLY_DEAD_SCOPE: >-
    Only the global anchor-only PSD certificate using a prime subset that
    misses a live top prime column. No original arithmetic target is killed.
  REPAIR: >-
    Keep the entire remaining kernel block, use sufficient additional
    constraints, or provide another budget matrix with a proved cost on mu.
  SOURCE_ANALYTIC_PREMISES: CONDITIONAL_UNCHANGED
META_CLOSEOUT:
  WHAT_BECAME_SMALLER: >-
    The free-corrector construction problem is solved exactly; its only
    remaining full-source coefficient is identified as the original energy.
  WHAT_WAS_KILLED: TWO_PRIME_OR_INSUFFICIENT_PRIME_GLOBAL_ANCHOR_PSD_SCHEME
  WHAT_NOT_TO_REPEAT: >-
    Free multiplier searches, increasing transverse penalties, or counting
    simultaneous diagonalization as an arithmetic power improvement.
  MINIMAL_MISSING_IDENTITY: NONE_NEW_REQUIRED
  MINIMAL_MISSING_INEQUALITY: ORIGINAL_MB34_OR_MC23_AT_TARGET_BUDGET
  PREDICTION_FATES: P1_P2_P3_P4_P5_CONFIRMED_BY_EXACT_FINITE_CHECKS
  FULL_CONSUMER_PROGRESS: NONE
  MEMORY_ENTRY:
    target: TARGET_BUDGET_MIXED_CORRECTOR
    status: OPEN
    cognitive_operator_used: DUALIZE
    invariant_learned: EVERY_SOURCE_NULL_CORRECTION_PRESERVES_BUDGET_MINUS_ENERGY
    forbidden_future_move: PAY_SOURCE_DIRECTION_WITH_TRANSVERSE_SQUARES
    next_decisive_test: GENUINE_JOINT_ARITHMETIC_UPPER_BOUND_NOT_ANOTHER_Y
```

## Приложение A. Регистрация перед конечным запуском

Следующий JSON был записан до создания и запуска нового проверочного скрипта. Время — метка рабочей среды, не обещание фонового выполнения. Для воспроизведения сохрани JSON как `registration.json` рядом с кодом из приложения C. Код и JSON ниже исчерпывают новые вычислительные входы; исходные источники нужны для смыслового аудита диагностической ячейки.

```json
{
  "registered_before_new_exact_runs": true,
  "utc": "2026-10-09T09:36:19.180205+00:00",
  "predictions": {
    "P1": "On every finite divisor-closed good ideal set, Z A_p = D_p Z and Z mu=e_1.",
    "P2": "The explicit mixed multiplier eliminates exactly all blocks touching the nonkernel divisor coordinates and leaves the kernel block unchanged.",
    "P3": "At the full norm-49 diagnostic source, omission of the conjugate prime of norm 7 leaves an exact negative certificate value -4/13 for any anchor budget.",
    "P4": "With all local annihilators, the constructed residual is (budget-energy)e1e1*+tau Z*QZ. Budgets below/equal/above the exact energy have the predicted inertia.",
    "P5": "Deleting the second prime-power shift fails at p^2; altering mu(pq) is detected. None of the exact finite tests certifies a cofinal moment."
  },
  "pins": {
    "PROSHKA_OPERATOR_RETHINK_Q05_FOLLOWUP.md": {
      "sha256": "e7c7dd64105f935f1d0fba411b9f8c44929a77cf8dbc0e26b4dfc37fbff713fb",
      "bytes": 44455,
      "lines": 711
    },
    "PROSHKA_RATIONAL_HIGH_VALUES_Q05.txt": {
      "sha256": "04569d150a39475d0e16dcc5a08e61fda25e1b338d9b76cf5ce58c6424902581",
      "bytes": 950620,
      "lines": 19252
    }
  }
}
```

## Приложение B. Фактический вывод точного запуска

Среда: Python и установленный SymPy; только целочисленные и рациональные проверки, без округлённых собственных значений.

```json
{
  "basis_bound_83_size": 25,
  "basis_bound_83_prime_ideals": 21,
  "source_rows": 18,
  "source_energy": "8/13",
  "omitted_prime_certificate": "-4/13",
  "source_congruence_pivots": [
    "-1/13",
    "0",
    "1/13"
  ],
  "checks_by_group": {
    "preregistration": 1,
    "basis": 2,
    "factorization": 33,
    "inverse": 4,
    "mobius": 2,
    "similarity": 28,
    "annihilator": 28,
    "commuting": 231,
    "corrector_identity": 14,
    "null_source": 12,
    "residual_congruence": 36,
    "source_budget_invariant": 36,
    "full_inertia_certificate": 12,
    "source_primes": 1,
    "source_scale_band": 1,
    "source_rows": 1,
    "source_zero_masks": 1,
    "source_cross_zeros": 18,
    "source_energy": 1,
    "omitted_prime_kernel": 2,
    "omitted_prime_negative": 3,
    "source_exact_inertia": 3,
    "planted_power_deletion": 1,
    "planted_mobius_corruption": 1,
    "budget": 2
  },
  "total_boolean_checks": 474,
  "scope": "EXACT_FINITE_ALGEBRA_AND_ONE_COMPLETE_DIAGNOSTIC_SOURCE_NOT_COFINAL_MOMENT"
}
```

## Приложение C. Полный проверочный код

Сохрани блок как `check.py`, а JSON из приложения A — как `registration.json` в той же папке. Например, `{workdir}` означает выбранную папку проверки: при `{workdir}=/tmp/mixed-corrector` оба файла лежат в `/tmp/mixed-corrector`. Из этой папки код запускается командой `python3 check.py` в среде с SymPy. Скрипт ничего не меняет в исходных файлах и печатает результаты в стандартный вывод.

SHA-256 выполненного скрипта: `7cfe31e83816edbfb0b11f661d7a69adbeeb18660ff98af643c4e651f5afda6c`.

```python
"""Exact finite checks for the mixed Möbius-annihilator corrector.
Requires Python 3.10+ and SymPy; no numerical eigenvalue computation.
The norm-49 example is a complete diagnostic source, not a cofinal bound.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
from math import isqrt
from pathlib import Path
import json
import sympy as s

Ideal = tuple[int, int]
ONE: Ideal = (1, 0)
checks: Counter[str] = Counter()

def check(condition: bool, group: str) -> None:
    if not condition:
        raise AssertionError(f"Failed exact check: {group}")
    checks[group] += 1

def norm(z: Ideal) -> int:
    a, b = z
    return a*a-a*b+b*b

def mul(z: Ideal, w: Ideal) -> Ideal:
    a,b=z; c,d=w
    return a*c-b*d, a*d+b*c-b*d

def div(z: Ideal, w: Ideal) -> Ideal | None:
    a,b=w; c,d=mul(z,(a-b,-b)); q=norm(w)
    return (c//q,d//q) if c%q==0 and d%q==0 else None

def basis(bound: int) -> list[Ideal]:
    h=2*isqrt(bound)+3
    out=[(a,b) for a in range(-h,h+1) for b in range(-h,h+1)
         if a%3==1 and b%3==0 and 0<norm((a,b))<=bound
         and norm((a,b))%2 and norm((a,b))%3]
    return sorted(out,key=lambda z:(norm(z),z))

def data(bound: int):
    ideals=basis(bound); N=len(ideals); ix={n:i for i,n in enumerate(ideals)}
    check(ideals[0]==ONE,'basis')
    primes=[n for n in ideals[1:] if not any(
        norm(d)>1 and norm(d)<norm(n) and div(n,d) is not None for d in ideals)]
    val={}
    for n in ideals:
        row=[]
        for p in primes:
            v=0; m=n
            while div(m,p) is not None:
                m=div(m,p); v+=1
            row.append(v)
        val[n]=row
        check(__import__('math').prod(norm(p)**v for p,v in zip(primes,row))==norm(n),'factorization')
    mu={n:0 if any(v>1 for v in val[n]) else (-1)**sum(val[n]) for n in ideals}
    Z=s.Matrix(N,N,lambda i,j: int(div(ideals[i],ideals[j]) is not None))
    inv=s.Matrix(N,N,lambda i,j: mu.get(div(ideals[i],ideals[j]),0))
    check(Z*inv==s.eye(N),'inverse'); check(inv*Z==s.eye(N),'inverse')
    e=s.eye(N)[:,0]; m=s.Matrix([mu[n] for n in ideals])
    check(Z*m==e,'mobius')
    As=[]; Ds=[]
    for k,p in enumerate(primes):
        A=s.zeros(N); D=s.diag(*[val[n][k] for n in ideals])
        for i,n in enumerate(ideals):
            A[i,i]=val[n][k]; r=n
            for _ in range(val[n][k]):
                r=div(r,p); A[i,ix[r]]+=1
        check(Z*A==D*Z,'similarity'); check(A*m==s.zeros(N,1),'annihilator')
        As.append(A); Ds.append(D)
    for i,A in enumerate(As):
        for B in As[i+1:]:
            check(A*B==B*A,'commuting')
    return ideals,ix,primes,mu,Z,inv,e,m,As,Ds

def correction(G,Z,inv,e,As,Ds,active,tau):
    N=G.rows
    A=sum((As[i] for i in active),s.zeros(N))
    D=sum((Ds[i] for i in active),s.zeros(N))
    F=s.diag(*[int(D[i,i]==0) for i in range(N)])
    K=s.eye(N)-F
    Ddag=s.diag(*[1/D[i,i] if D[i,i]!=0 else 0 for i in range(N)])
    H=inv.H*G*inv
    B=-s.Rational(1,2)*K*H*K-K*H*F-tau*s.Rational(1,2)*K
    Y=Z.H*Ddag*B*Z
    null=A.H*Y+Y.H*A
    target=Z.H*(F*H*F-tau*K)*Z
    check(G+null==target,'corrector_identity')
    return null,F,K,H,Y

def main():
    check(Path(__file__).with_name('registration.json').exists(),'preregistration')
    source=None
    for bound in (30,83):
        ideals,ix,primes,mu,Z,inv,e,m,As,Ds=data(bound)
        N=len(ideals)
        # Deterministic complex Gram tests; these are algebraic controls only.
        T=s.Matrix(3,N,lambda i,j:s.Integer(((i+2)*(j+3))%7-3)
                   +s.I*s.Integer((2*i+3*j)%5-2))
        G=T.H*T
        for active in ([],list(range(min(2,len(primes)))),list(range(len(primes)))):
            for tau in (s.Rational(1,3),s.Integer(2)):
                null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,active,tau)
                check((m.H*null*m)[0]==0,'null_source')
                # Independent directly transformed residual, at 3 budgets.
                energy=(m.H*G*m)[0]
                for delta in (-1,0,1):
                    budget=energy+delta
                    R=budget*e*e.H-G-null
                    rhs=budget*e*e.H-F*H*F+tau*K
                    check(inv.H*R*inv==rhs,'residual_congruence')
                    check((m.H*R*m)[0]==delta,'source_budget_invariant')
                    if len(active)==len(primes):
                        check(rhs==s.diag(delta,*([tau]*(N-1))),'full_inertia_certificate')
        if bound==83:
            source=(ideals,ix,primes,mu,Z,inv,e,m,As,Ds)
    ideals,ix,primes,mu,Z,inv,e,m,As,Ds=source
    N=len(ideals)
    pi=(-2,-3); pib=(1,3); sigma=(1,-3)
    check(norm(pi)==norm(pib)==7 and norm(sigma)==13,'source_primes')
    check(78**25<=49**28 and 78**100>=49**111,'source_scale_band')
    # All 18 elements of norm 49, not a selected subset.
    rows=[(a,b) for a in range(-16,17) for b in range(-16,17) if norm((a,b))==49]
    check(len(rows)==18,'source_rows')
    masks=[(int(div(u,pi) is None),int(div(u,pib) is None)) for u in rows]
    check(Counter(masks)==Counter({(0,0):6,(1,0):6,(0,1):6}),'source_zero_masks')
    # W(7/78)=2, nu=1, rho(1)=1. Cross-terms vanish by actual zeros.
    G=s.zeros(N)
    for a,b in masks:
        check(a*b==0,'source_cross_zeros')
        G[ix[pi],ix[pi]]+=s.Rational(4,78)*a
        G[ix[pib],ix[pib]]+=s.Rational(4,78)*b
    energy=(m.H*G*m)[0]
    check(energy==s.Rational(8,13),'source_energy')
    active=[primes.index(pi),primes.index(sigma)]
    null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,active,s.Integer(1))
    v=inv[:,ix[pib]]
    for i in active:
        check(As[i]*v==s.zeros(N,1),'omitted_prime_kernel')
    for budget in (s.Integer(0),s.Rational(8,13),s.Integer(10)**9):
        R=budget*e*e.H-G-null
        check((v.H*R*v)[0]==-s.Rational(4,13),'omitted_prime_negative')
    source_null,F,K,H,Y=correction(G,Z,inv,e,As,Ds,list(range(len(primes))),s.Integer(1))
    for delta in (-s.Rational(1,13),0,s.Rational(1,13)):
        R=(energy+delta)*e*e.H-G-source_null
        check(inv.H*R*inv==s.diag(delta,*([1]*(N-1))),'source_exact_inertia')
    # Planted failures: dropping p^2 and corrupting the p*q coefficient.
    Ap=As[primes.index(pi)]
    one_power=s.zeros(N)
    for i,n in enumerate(ideals):
        one_power[i,i]=Ap[i,i]
        q=div(n,pi)
        if q is not None:
            one_power[i,ix[q]]=1
    check((one_power*m)[ix[mul(pi,pi)]]==-1,'planted_power_deletion')
    bad=m.copy(); bad[ix[mul(pi,pib)]]=0
    check((Ap*bad)[ix[mul(pi,pib)]]==-1,'planted_mobius_corruption')
    # Exact exponent arithmetic for the old, still conditional, budget.
    rlo=s.Rational(28,25); rhi=s.Rational(113,100); eta=s.Rational(1,200)
    c0=s.Rational(1,10000)
    gaps=[eta-5*r*c0/6 for r in (rlo,rhi)]
    check(gaps==[s.Rational(46,9375),s.Rational(5887,1200000)],'budget')
    check(eta-5*rhi*c0/6-s.Rational(1,250)==s.Rational(1087,1200000),'budget')
    out={'basis_bound_83_size':N,'basis_bound_83_prime_ideals':len(primes),
         'source_rows':len(rows),'source_energy':str(energy),
         'omitted_prime_certificate':str(-s.Rational(4,13)),
         'source_congruence_pivots':['-1/13','0','1/13'],
         'checks_by_group':dict(checks),'total_boolean_checks':sum(checks.values()),
         'scope':'EXACT_FINITE_ALGEBRA_AND_ONE_COMPLETE_DIAGNOSTIC_SOURCE_NOT_COFINAL_MOMENT'}
    print(json.dumps(out,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
```
